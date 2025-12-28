/-

  Step 1 (prerequisite layer): the λ-dependent semiclassical symbol class `S^m_λ`

  This file formalizes Definition 3.2 of CW's TwoChartEgorov paper in a Mathlib-idiomatic way:
    • a “Japanese bracket” weight ⟨τ⟩ := √(1+τ^2),
    • a mixed iterated partial derivative operator ∂_t^α ∂_τ^β,
    • the λ-dependent symbol predicate `SmLambda`,
    • and (Remark 3.3) the fundamental closure of `SmLambda` under multiplication.

  Technical note (faithful to semiclassical analysis practice):
    To compress a finite sum of monomials (h⁻¹)^{Mᵢ} into a single monomial factor
    (h⁻¹)^M with M := max Mᵢ, we assume `h0 ≤ 1`. Then h ∈ (0,h0] implies 1 ≤ h⁻¹.

-/

import Mathlib
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open scoped BigOperators

namespace TwoChartEgorov

-- import Mathlib.Analysis.SpecialFunctions.JapaneseBracket - do not reduplicate API

/-- Japanese bracket `⟨x⟩ := √(1+x^2)` (used for τ-weights). -/
noncomputable def japaneseBracket (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

lemma japaneseBracket_nonneg (x : ℝ) : 0 ≤ japaneseBracket x := by
  simp [japaneseBracket]

lemma one_le_japaneseBracket (x : ℝ) : (1 : ℝ) ≤ japaneseBracket x := by
  have hx : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hx
  simpa [japaneseBracket] using this

lemma japaneseBracket_pos (x : ℝ) : 0 < japaneseBracket x := by
  have h : (1 : ℝ) ≤ japaneseBracket x := one_le_japaneseBracket x
  linarith

/-- Mixed iterated derivative:
`∂_t^α ∂_τ^β a(h,t,τ)`.

Implemented using separate one-variable iterated derivatives. -/
noncomputable def dtdτ (α β : ℕ) (a : ℝ → ℝ → ℝ → ℂ) (h t τ : ℝ) : ℂ :=
  (iteratedDeriv α (fun t' : ℝ => (iteratedDeriv β (fun τ' : ℝ => a h t' τ') τ)) t)

/-- The λ-dependent symbol class `S^m_λ(T*Y)` (Definition 3.2 in the paper).

Uniformity in the semiclassical parameter is over `h ∈ (0,h0]`, represented as `h ∈ Ioc 0 h0`.

The “tempered in h^{-1}” condition is represented by the factor `(h⁻¹)^M` with `M : ℕ`. -/
def SmLambda (Y : Set ℝ) (h0 m : ℝ) (a : ℝ → ℝ → ℝ → ℂ) : Prop :=
  (∀ h : ℝ, ContDiff ℝ ⊤ (fun p : ℝ × ℝ => a h p.1 p.2)) ∧
    ∀ α β : ℕ,
      ∃ C : ℝ, ∃ M : ℕ, 0 ≤ C ∧
        ∀ ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
          ∀ ⦃t : ℝ⦄, t ∈ Y →
            ∀ τ : ℝ,
              ‖dtdτ α β a h t τ‖ ≤ C * (h⁻¹) ^ M * (japaneseBracket τ) ^ (m - (β : ℝ))

namespace SmLambda

open scoped BigOperators

variable {Y : Set ℝ} {h0 : ℝ}
variable {m₁ m₂ : ℝ}
variable {a b : ℝ → ℝ → ℝ → ℂ}

/-!
### Auxiliary calculus lemmas

We need (1) smooth dependence of `τ ↦ iteratedDeriv n (a h t ·)` on the parameter `t`,
and (2) a one-dimensional Leibniz rule for `iteratedDeriv` (under `ContDiff` hypotheses).

These are packaged locally to keep the main `mul` proof readable.
-/

lemma contDiff_iteratedDeriv_snd
    (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ⊤ f) (n : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => iteratedDeriv n (fun τ : ℝ => f (p.1, τ)) p.2) := by
  classical
  induction n with
  | zero =>
      simpa using hf
  | succ n IH =>
      -- Write the `(n+1)`-th τ-derivative as the derivative of the `n`-th τ-derivative.
      -- Use `ContDiff.fderiv_apply` for the τ-derivative and then evaluate at `1 : ℝ` to get `deriv`.
      have hPk : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => iteratedDeriv n (fun τ : ℝ => f (p.1, τ)) p.2) :=
        IH
      -- Define `Pk (t,τ) := ∂_τ^n f(t,τ)` and view it as a function of `(p,τ')` ignoring `p.2`.
      let Pk : ℝ × ℝ → ℂ := fun p : ℝ × ℝ => iteratedDeriv n (fun τ : ℝ => f (p.1, τ)) p.2
      have hPk' : ContDiff ℝ ⊤ Pk := hPk
      -- The uncurried function needed for `fderiv_apply` is `((p,τ'), ↦ Pk (p.1, τ'))`.
      have h_uncurry :
          ContDiff ℝ ⊤ (Function.uncurry (fun p : ℝ × ℝ => fun τ : ℝ => Pk (p.1, τ))) := by
        -- This is `Pk` composed with the smooth map `((p,τ'), ↦ (p.1, τ'))`.
        have hmap : ContDiff ℝ ⊤ (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) := by
          fun_prop
        simpa [Function.uncurry, Pk] using hPk'.comp hmap
      have hg : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := by
        simpa using (contDiff_snd : ContDiff ℝ ⊤ (Prod.snd : (ℝ × ℝ) → ℝ))
      have hk : ContDiff ℝ ⊤ (fun _p : ℝ × ℝ => (1 : ℝ)) := by
        simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _p : ℝ × ℝ => (1 : ℝ)))
      have hderiv_fun :
          ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
            fderiv ℝ (fun τ : ℝ => Pk (p.1, τ)) (p.2) (1 : ℝ)) :=
        (ContDiff.fderiv_apply (f := fun p : ℝ × ℝ => fun τ : ℝ => Pk (p.1, τ))
            (g := fun p : ℝ × ℝ => p.2) (k := fun _p : ℝ × ℝ => (1 : ℝ))
            h_uncurry hg hk (by simp))
      -- Convert `fderiv · · 1` to `deriv` using `fderiv_eq_smul_deriv`.
      have hderiv_fun' :
          ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
            deriv (fun τ : ℝ => Pk (p.1, τ)) (p.2)) := by
        -- `ContDiff` has no direct `congr`, so go pointwise (`ContDiffAt`) and use
        -- `ContDiffAt.congr_of_eventuallyEq` with a (trivial) `EventuallyEq`.
        rw [contDiff_iff_contDiffAt] at hderiv_fun ⊢
        intro p
        refine (hderiv_fun p).congr_of_eventuallyEq ?_
        -- The two functions are pointwise equal everywhere, hence eventually equal.
        refine Filter.Eventually.of_forall ?_
        intro q
        -- `fderiv_eq_smul_deriv` gives `(fderiv ...) 1 = 1 • deriv ...`.
        -- Rewrite to `deriv = fderiv ... 1`.
        simp
      -- Finally, rewrite `iteratedDeriv (n+1)` as `deriv (iteratedDeriv n ·)` in τ.
      -- Here `Pk (p.1, τ)` is exactly `iteratedDeriv n (τ ↦ f(p.1,τ)) τ`.
      simpa [Pk, iteratedDeriv_succ] using hderiv_fun'

lemma iteratedDeriv_mul
    (n : ℕ) (f g : ℝ → ℂ) (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (x : ℝ) :
    iteratedDeriv n (fun y => f y * g y) x =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x) := by
  classical
  induction n generalizing x with
  | zero =>
      simp
  | succ n IH =>
      have hf' : ContDiff ℝ n f := hf.of_le (by
        -- cast `n ≤ n+1` into `WithTop ℕ∞`
        exact_mod_cast (Nat.le_succ n))
      have hg' : ContDiff ℝ n g := hg.of_le (by
        exact_mod_cast (Nat.le_succ n))
      -- Differentiate the induction hypothesis.
      have hIHfun :
          iteratedDeriv n (fun y => f y * g y) =
            fun x =>
              ∑ i ∈ Finset.range (n + 1),
                (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x) := by
        funext x
        simpa using IH (hf := hf') (hg := hg') x
      -- Use `iteratedDeriv_succ` and compute the derivative of the finite sum.
      have hdiff_term :
          ∀ i ∈ Finset.range (n + 1),
            DifferentiableAt ℝ
              (fun x =>
                (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x)) x := by
        intro i hi
        -- `ContDiff` gives differentiability of the relevant iterated derivatives.
        have hdf_i : DifferentiableAt ℝ (iteratedDeriv i f) x := by
          -- `i < n+1`
          have hi' : (i : WithTop ℕ∞) < (n + 1 : WithTop ℕ∞) := by
            -- `i < n+1` as naturals from `hi : i ∈ range (n+1)`
            have : i < n + 1 := Finset.mem_range.1 hi
            exact Nat.cast_lt.mpr this
          exact (hf.differentiable_iteratedDeriv i hi') x
        have hdg_ni : DifferentiableAt ℝ (iteratedDeriv (n - i) g) x := by
          have : n - i < n + 1 := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)
          have hi' : (n - i : WithTop ℕ∞) < (n + 1 : WithTop ℕ∞) := by
            exact Nat.cast_lt.mpr this
          exact (hg.differentiable_iteratedDeriv (n - i) hi') x
        -- Build differentiability of the product and the left constant multiplication.
        have hmul : DifferentiableAt ℝ (fun x => iteratedDeriv i f x * iteratedDeriv (n - i) g x) x :=
          hdf_i.mul hdg_ni
        -- left multiplication by a constant in a normed algebra is differentiable
        simpa [mul_assoc] using (hmul.const_mul (Nat.choose n i : ℂ))
      calc
        iteratedDeriv (n + 1) (fun y => f y * g y) x
            = deriv (iteratedDeriv n (fun y => f y * g y)) x := by
                -- `iteratedDeriv_succ` is a function-level lemma
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  (congrArg (fun h => h x)
                    (iteratedDeriv_succ (n := n) (f := fun y => f y * g y)))
        _ = deriv (fun x =>
              ∑ i ∈ Finset.range (n + 1),
                (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x)) x := by
              simp [hIHfun]
        _ = ∑ i ∈ Finset.range (n + 1),
              deriv (fun x =>
                (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x)) x := by
              -- derivative of a finite sum
              simpa using (deriv_fun_sum (u := Finset.range (n + 1))
                (A := fun i x =>
                  (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x))
                (x := x) hdiff_term)
        _ = ∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℂ) *
                (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x +
                  iteratedDeriv i f x * iteratedDeriv (n - i + 1) g x) := by
              -- termwise product rule; use `deriv_const_mul` and `deriv_fun_mul`.
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hdf_i : DifferentiableAt ℝ (iteratedDeriv i f) x := by
                have hi' : (i : WithTop ℕ∞) < (n + 1 : WithTop ℕ∞) := by
                  have : i < n + 1 := Finset.mem_range.1 hi
                  exact Nat.cast_lt.mpr this
                exact (hf.differentiable_iteratedDeriv i hi') x
              have hdg_ni : DifferentiableAt ℝ (iteratedDeriv (n - i) g) x := by
                have : n - i < n + 1 := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)
                have hi' : (n - i : WithTop ℕ∞) < (n + 1 : WithTop ℕ∞) := by
                  exact Nat.cast_lt.mpr this
                exact (hg.differentiable_iteratedDeriv (n - i) hi') x
              have hmul : DifferentiableAt ℝ (fun x => iteratedDeriv i f x * iteratedDeriv (n - i) g x) x :=
                hdf_i.mul hdg_ni
              -- constants and product rule
              have hderiv_i :
                  deriv (iteratedDeriv i f) x = iteratedDeriv (i + 1) f x := by
                simpa using
                  (congrArg (fun h => h x)
                    (iteratedDeriv_succ (n := i) (f := f))).symm
              have hderiv_ni :
                  deriv (iteratedDeriv (n - i) g) x = iteratedDeriv (n - i + 1) g x := by
                simpa [Nat.add_assoc] using
                  (congrArg (fun h => h x)
                    (iteratedDeriv_succ (n := n - i) (f := g))).symm
              -- compute (keep the constant coefficient on the left to match `deriv_const_mul`)
              have :
                  deriv (fun x =>
                      (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x)) x
                    =
                    (Nat.choose n i : ℂ) *
                      (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x +
                        iteratedDeriv i f x * iteratedDeriv (n - i + 1) g x) := by
                -- first peel off the constant, then use product rule
                have hmul' :
                    deriv (fun x => iteratedDeriv i f x * iteratedDeriv (n - i) g x) x =
                      deriv (iteratedDeriv i f) x * iteratedDeriv (n - i) g x +
                        iteratedDeriv i f x * deriv (iteratedDeriv (n - i) g) x := by
                  simpa using (deriv_fun_mul (c := iteratedDeriv i f) (d := iteratedDeriv (n - i) g)
                    (x := x) hdf_i hdg_ni)
                -- assemble
                calc
                  deriv (fun x =>
                      (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n - i) g x)) x
                      = (Nat.choose n i : ℂ) *
                          deriv (fun x => iteratedDeriv i f x * iteratedDeriv (n - i) g x) x := by
                          simp
                  _ = (Nat.choose n i : ℂ) *
                        (deriv (iteratedDeriv i f) x * iteratedDeriv (n - i) g x +
                          iteratedDeriv i f x * deriv (iteratedDeriv (n - i) g) x) := by
                        simp [hmul']
                  _ = (Nat.choose n i : ℂ) *
                        (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x +
                          iteratedDeriv i f x * iteratedDeriv (n - i + 1) g x) := by
                        simp [hderiv_i, hderiv_ni]
              -- finish
              simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc] using this
        _ = ∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n + 1 - i) g x) +
            ∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℂ) * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x) := by
              -- Distribute the coefficient across the sum, then rewrite `n - i + 1` as `n + 1 - i`
              -- using `i ≤ n` for `i ∈ range (n+1)`.
              have hsub : ∀ i ∈ Finset.range (n + 1), n - i + 1 = n + 1 - i := by
                intro i hi
                have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
                simpa using (Nat.succ_sub hi_le).symm
              -- First distribute `mul_add`, then split the sum.
              calc
                (∑ i ∈ Finset.range (n + 1),
                    (Nat.choose n i : ℂ) *
                      (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x +
                        iteratedDeriv i f x * iteratedDeriv (n - i + 1) g x))
                    =
                    (∑ i ∈ Finset.range (n + 1),
                      (Nat.choose n i : ℂ) *
                        (iteratedDeriv i f x * iteratedDeriv (n - i + 1) g x)) +
                      ∑ i ∈ Finset.range (n + 1),
                        (Nat.choose n i : ℂ) *
                          (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x) := by
                    -- `mul_add` + `Finset.sum_add_distrib`, plus a commutativity swap to match our order.
                    simp [mul_add, Finset.sum_add_distrib, add_comm, mul_left_comm, mul_comm]
                _ =
                    (∑ i ∈ Finset.range (n + 1),
                      (Nat.choose n i : ℂ) *
                        (iteratedDeriv i f x * iteratedDeriv (n + 1 - i) g x)) +
                      ∑ i ∈ Finset.range (n + 1),
                        (Nat.choose n i : ℂ) *
                          (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x) := by
                    -- rewrite `n - i + 1` to `n + 1 - i` inside the first sum
                    refine congrArg (fun A =>
                      A + ∑ i ∈ Finset.range (n + 1),
                        (Nat.choose n i : ℂ) *
                          (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x)) ?_
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    simp [hsub i hi, mul_left_comm]
                _ = _ := by
                    -- swap the two sums back to the order in the goal
                    ac_rfl
        _ = ∑ i ∈ Finset.range (n + 2),
              ((n + 1).choose i : ℂ) * (iteratedDeriv i f x * iteratedDeriv (n + 1 - i) g x) := by
              -- Apply `Finset.sum_choose_succ_mul` with `f i j = iteratedDeriv i f x * iteratedDeriv j g x`.
              -- Rewrite `n + 1` as `n.succ` and simplify casts.
              simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
                (Finset.sum_choose_succ_mul (R := ℂ)
                  (f := fun i j => iteratedDeriv i f x * iteratedDeriv j g x) n).symm
      -- `calc` already matches the goal.

lemma iteratedDeriv_finset_sum
    (n : ℕ) {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ) (x : ℝ)
    (hF : ∀ i ∈ s, ContDiffAt ℝ n (F i) x) :
    iteratedDeriv n (fun t => ∑ i ∈ s, F i t) x = ∑ i ∈ s, iteratedDeriv n (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- `∑ i ∈ ∅, F i t` is the constant `0` function, whose iterated derivatives are `0`.
      simp [iteratedDeriv_const]
  | @insert i s hi IH =>
      have hFi : ContDiffAt ℝ n (F i) x := hF i (by simp [hi])
      have hFs : ∀ j ∈ s, ContDiffAt ℝ n (F j) x := fun j hj => hF j (by simp [hj])
      have hsum : ContDiffAt ℝ n (fun t : ℝ => ∑ j ∈ s, F j t) x := ContDiffAt.sum hFs
      -- First rewrite the goal using `Finset.sum_insert`, then use additivity of `iteratedDeriv`.
      simp [Finset.sum_insert, hi]
      calc
        iteratedDeriv n (fun t : ℝ => F i t + ∑ j ∈ s, F j t) x
            = iteratedDeriv n (F i) x + iteratedDeriv n (fun t : ℝ => ∑ j ∈ s, F j t) x := by
                simpa using
                  (iteratedDeriv_add (n := n) (f := F i) (g := fun t : ℝ => ∑ j ∈ s, F j t)
                    (x := x) hFi hsum)
        _ = iteratedDeriv n (F i) x + ∑ j ∈ s, iteratedDeriv n (F j) x := by
              simp [IH hFs]

lemma dtdτ_mul
    {a b : ℝ → ℝ → ℝ → ℂ} {h : ℝ} (ha : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => a h p.1 p.2))
    (hb : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => b h p.1 p.2)) (α β : ℕ) (t τ : ℝ) :
    dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ =
      ∑ p ∈ (Finset.range (α + 1)).product (Finset.range (β + 1)),
        (Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
          dtdτ p.1 p.2 a h t τ * dtdτ (α - p.1) (β - p.2) b h t τ := by
  classical
  -- τ-Leibniz first, then t-Leibniz, keeping track of binomial coefficients.
  -- Abbreviations for the (t,τ)-functions at fixed `h`.
  let A : ℝ × ℝ → ℂ := fun p => a h p.1 p.2
  let B : ℝ × ℝ → ℂ := fun p => b h p.1 p.2
  have hA : ContDiff ℝ ⊤ A := ha
  have hB : ContDiff ℝ ⊤ B := hb
  -- Pointwise τ-Leibniz expansion at each `t'`.
  have hτ (t' : ℝ) :
      iteratedDeriv β (fun τ' : ℝ => a h t' τ' * b h t' τ') τ =
        ∑ j ∈ Finset.range (β + 1),
          (Nat.choose β j : ℂ) *
            (iteratedDeriv j (fun τ' : ℝ => a h t' τ') τ *
              iteratedDeriv (β - j) (fun τ' : ℝ => b h t' τ') τ) := by
    have haτinfty : ContDiff ℝ ⊤ (fun τ' : ℝ => a h t' τ') := by
      simpa [A] using hA.comp (contDiff_prodMk_right (e₀ := t'))
    have hbτinfty : ContDiff ℝ ⊤ (fun τ' : ℝ => b h t' τ') := by
      simpa [B] using hB.comp (contDiff_prodMk_right (e₀ := t'))
    have haτ : ContDiff ℝ β (fun τ' : ℝ => a h t' τ') :=
      haτinfty.of_le (by simp)
    have hbτ : ContDiff ℝ β (fun τ' : ℝ => b h t' τ') :=
      hbτinfty.of_le (by simp)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (iteratedDeriv_mul β (fun τ' : ℝ => a h t' τ') (fun τ' : ℝ => b h t' τ') haτ hbτ τ)
  -- Rewrite the τ-derivative as a finite sum of products, then take `α` t-derivatives.
  have hτfun :
      (fun t' : ℝ => iteratedDeriv β (fun τ' : ℝ => a h t' τ' * b h t' τ') τ) =
        fun t' : ℝ =>
          ∑ j ∈ Finset.range (β + 1),
            (Nat.choose β j : ℂ) *
              (iteratedDeriv j (fun τ' : ℝ => a h t' τ') τ *
                iteratedDeriv (β - j) (fun τ' : ℝ => b h t' τ') τ) := by
    funext t'
    exact hτ t'
  -- Now apply `α` t-derivatives and expand.
  -- For each `j`, set the `t`-functions `Aj` and `Bj`.
  let Aj : ℕ → ℝ → ℂ := fun j t' => iteratedDeriv j (fun τ' : ℝ => a h t' τ') τ
  let Bj : ℕ → ℝ → ℂ := fun j t' => iteratedDeriv (β - j) (fun τ' : ℝ => b h t' τ') τ
  have hAj_contDiff (j : ℕ) :
      ContDiff ℝ ⊤ (Aj j) := by
    -- `Aj j` is the restriction to `τ` of the smooth function `(t,τ) ↦ ∂_τ^j A(t,τ)`.
    have hP : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => iteratedDeriv j (fun τ' : ℝ => A (p.1, τ')) p.2) :=
      contDiff_iteratedDeriv_snd A hA j
    -- restrict to the slice `τ`
    simpa [Aj, A] using hP.comp (contDiff_prodMk_left (f₀ := τ))
  have hBj_contDiff (j : ℕ) :
      ContDiff ℝ ⊤ (Bj j) := by
    have hP : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => iteratedDeriv (β - j) (fun τ' : ℝ => B (p.1, τ')) p.2) :=
      contDiff_iteratedDeriv_snd B hB (β - j)
    simpa [Bj, B] using hP.comp (contDiff_prodMk_left (f₀ := τ))
  -- Expand the outer `iteratedDeriv α` over the finite τ-sum.
  have ht_sum :
      iteratedDeriv α
          (fun t' : ℝ =>
            ∑ j ∈ Finset.range (β + 1),
              (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t
        =
        ∑ j ∈ Finset.range (β + 1),
          iteratedDeriv α (fun t' : ℝ => (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t := by
    -- Use additivity of `iteratedDeriv` for finite sums.
    -- Each summand is `C^α` since `Aj` and `Bj` are `C^∞`.
    have hC : ∀ j ∈ Finset.range (β + 1),
        ContDiffAt ℝ α (fun t' : ℝ => (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t := by
      intro j hj
      have hAjα : ContDiffAt ℝ (α : WithTop ℕ∞) (Aj j) t :=
        ((hAj_contDiff j).contDiffAt (x := t)).of_le (by simp)
      have hBjα : ContDiffAt ℝ (α : WithTop ℕ∞) (Bj j) t :=
        ((hBj_contDiff j).contDiffAt (x := t)).of_le (by simp)
      -- product and left constant multiplication preserve smoothness
      have hmul : ContDiffAt ℝ α (fun t' : ℝ => Aj j t' * Bj j t') t := hAjα.mul hBjα
      simpa [mul_assoc] using (contDiffAt_const.mul hmul)
    simpa using (iteratedDeriv_finset_sum α (Finset.range (β + 1))
      (fun j t' => (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t hC)
  -- Expand each summand using the t-Leibniz rule, and then package as a product finset.
  have ht_term (j : ℕ) (hj : j ∈ Finset.range (β + 1)) :
      iteratedDeriv α (fun t' : ℝ => (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t =
        ∑ i ∈ Finset.range (α + 1),
          (Nat.choose α i : ℂ) * (Nat.choose β j : ℂ) *
            dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ := by
    -- Treat the β-binomial coefficient as a constant factor via the product rule with a constant function.
    have hconst : ContDiff ℝ α (fun _t' : ℝ => (Nat.choose β j : ℂ)) := contDiff_const
    have hprod : ContDiff ℝ α (fun t' : ℝ => Aj j t' * Bj j t') :=
      ((hAj_contDiff j).of_le (by simp)).mul ((hBj_contDiff j).of_le (by simp))
    -- First expand `α`-derivative of the product `(const) * (Aj*Bj)`.
    have h1 :=
      iteratedDeriv_mul α (fun _t' : ℝ => (Nat.choose β j : ℂ)) (fun t' : ℝ => Aj j t' * Bj j t')
        hconst hprod t
    -- Simplify: all higher derivatives of a constant vanish.
    -- Then expand the derivative of `Aj*Bj`.
    have h2 :=
      iteratedDeriv_mul α (Aj j) (Bj j)
        ((hAj_contDiff j).of_le (by simp))
        ((hBj_contDiff j).of_le (by simp))
        t
    -- Turn iterated derivatives of `Aj`/`Bj` into `dtdτ` by unfolding definitions.
    -- Also rewrite `β - j` in `Bj`.
    -- `h1` already has the right sum structure; we rewrite its inner `iteratedDeriv` using `h2`.
    -- Finally, commute coefficients.
    -- This is mostly `simp` plus associativity/commutativity of multiplication.
    -- (We keep the proof explicit to avoid timeouts.)
    -- Expand `h1` and substitute `h2` for the `α`-derivative of `Aj*Bj`.
    -- First, isolate the `i=0` contribution from `h1`.
    -- `iteratedDeriv_const` will kill the `i>0` terms.
    have hconst0 : iteratedDeriv 0 (fun _t' : ℝ => (Nat.choose β j : ℂ)) t = (Nat.choose β j : ℂ) := by
      simp [iteratedDeriv_const]
    have hconst_succ : ∀ i, 0 < i → iteratedDeriv i (fun _t' : ℝ => (Nat.choose β j : ℂ)) t = 0 := by
      intro i hi
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      simp [iteratedDeriv_const]
    -- Rewrite `h1` as a single term using the constant-derivative facts.
    -- Then plug in `h2`.
    -- This avoids relying on simp to normalize the whole sum.
    have h1' :
        iteratedDeriv α (fun t' : ℝ => (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t =
          (Nat.choose β j : ℂ) *
            iteratedDeriv α (fun t' : ℝ => Aj j t' * Bj j t') t := by
      -- `h1` is the binomial sum; only the `i = 0` term survives since higher iterated
      -- derivatives of a constant are `0`.
      refine h1.trans ?_
      classical
      -- isolate the `i = 0` term in the Leibniz sum
      rw [Finset.sum_eq_single 0]
      · -- evaluate the surviving term
        simp [hconst0, mul_left_comm]
      · intro i hi hne
        have hi_pos : 0 < i := Nat.pos_of_ne_zero hne
        simp [hconst_succ i hi_pos]
      · intro h0
        -- contradiction: `0 ∈ range (α+1)`
        simpa using (h0 (by simp : (0 : ℕ) ∈ Finset.range (α + 1)))
    -- Now use `h2` for the derivative of `Aj*Bj`.
    -- Note: `h2` has coefficients `(Nat.choose α i : ℂ)` already.
    -- Finally rearrange factors to match the statement.
    -- Turn `iteratedDeriv i (Aj j) t` into `dtdτ i j a h t τ`, similarly for `Bj`.
    -- `Bj j` is `τ`-derivative order `β-j`.
    have h2' :
        iteratedDeriv α (fun t' : ℝ => Aj j t' * Bj j t') t =
          ∑ i ∈ Finset.range (α + 1),
            (Nat.choose α i : ℂ) *
              (dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ) := by
      -- `h2` is exactly this after unfolding `Aj`, `Bj`, and `dtdτ`.
      -- Expand `h2` and normalize.
      -- `dtdτ` is `iteratedDeriv` in `t` of an `iteratedDeriv` in `τ`.
      simpa [Aj, Bj, dtdτ, mul_assoc, mul_left_comm, mul_comm] using h2
    -- Combine `h1'` and `h2'`, then commute coefficients.
    calc
      iteratedDeriv α (fun t' : ℝ => (Nat.choose β j : ℂ) * (Aj j t' * Bj j t')) t
          = (Nat.choose β j : ℂ) * iteratedDeriv α (fun t' : ℝ => Aj j t' * Bj j t') t := h1'
      _ = (Nat.choose β j : ℂ) *
            (∑ i ∈ Finset.range (α + 1),
              (Nat.choose α i : ℂ) *
                (dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ)) := by
            simp [h2']
      _ = ∑ i ∈ Finset.range (α + 1),
            (Nat.choose α i : ℂ) * (Nat.choose β j : ℂ) *
              dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ := by
            -- pull the common constant inside and reassociate/commute
            simp [Finset.mul_sum, mul_assoc, mul_left_comm]
  -- Put everything together.
  have : dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ =
        ∑ j ∈ Finset.range (β + 1),
          ∑ i ∈ Finset.range (α + 1),
            (Nat.choose α i : ℂ) * (Nat.choose β j : ℂ) *
              dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ := by
    -- unfold `dtdτ` and rewrite using `hτfun`, then use `ht_sum` and `ht_term`.
    unfold dtdτ
    -- rewrite the inner τ-derivative using `hτfun`
    rw [hτfun]
    -- expand the `t`-iterated derivative of the finite sum
    rw [ht_sum]
    -- expand each summand using `ht_term`
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa using ht_term j hj
  -- Repackage the double sum as a sum over the product finset.
  -- `Finset.sum_product` turns `∑ i, ∑ j` into `∑ (i,j)`; we match the order of `I`.
  -- Our `this` has outer sum over `j` then `i`; flip using `Finset.sum_product` and commutativity.
  -- First rewrite to the exact `Finset.range` product form.
  -- Swap the order of summation to match `Finset.sum_product` for `(range (α+1)).product (range (β+1))`.
  have this' :
      dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ =
        ∑ i ∈ Finset.range (α + 1),
          ∑ j ∈ Finset.range (β + 1),
            (Nat.choose α i : ℂ) * (Nat.choose β j : ℂ) *
              dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ := by
    -- Avoid `simp` timeouts: commute the two finite sums with `Finset.sum_comm`.
    refine this.trans ?_
    -- `Finset.sum_comm` : (∑ j∈Sβ, ∑ i∈Sα, f j i) = (∑ i∈Sα, ∑ j∈Sβ, f j i)
    simpa using
      (Finset.sum_comm (s := Finset.range (β + 1)) (t := Finset.range (α + 1))
        (f := fun j i =>
          (Nat.choose α i : ℂ) * (Nat.choose β j : ℂ) *
            dtdτ i j a h t τ * dtdτ (α - i) (β - j) b h t τ))
  -- Turn the iterated sum into a sum over the product finset.
  -- (This lemma is much faster than `simp [Finset.sum_product, …]` here.)
  -- Use `Finset.sum_product` with an explicit uncurried summand.
  let F : (ℕ × ℕ) → ℂ := fun p =>
    (Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
      dtdτ p.1 p.2 a h t τ * dtdτ (α - p.1) (β - p.2) b h t τ
  -- rewrite the RHS of `this'` as `∑ i, ∑ j, F (i,j)` and then apply `Finset.sum_product`.
  refine this'.trans ?_
  -- `Finset.sum_product` is oriented from the product-sum to the iterated sum, so we use `symm`.
  simpa [F] using
    (Finset.sum_product (Finset.range (α + 1)) (Finset.range (β + 1)) F).symm

/-- If `h0 ≤ 1` and `h ∈ (0,h0]`, then `1 ≤ h⁻¹`. -/
lemma one_le_inv_of_mem_Ioc (hh0 : h0 ≤ 1) {h : ℝ} (hh : h ∈ Set.Ioc (0 : ℝ) h0) :
    (1 : ℝ) ≤ h⁻¹ := by
  have hhpos : 0 < h := (Set.mem_Ioc.1 hh).1
  have hhle  : h ≤ 1 := le_trans (Set.mem_Ioc.1 hh).2 hh0
  have : (1 : ℝ) ≤ h⁻¹ := (one_le_inv₀ (by exact hhpos)).2 hhle
  simpa using this

/-- Monotonicity of `M ↦ (h⁻¹)^M` when `1 ≤ h⁻¹`. -/
lemma pow_inv_mono_of_one_le {h : ℝ} (h1 : (1 : ℝ) ≤ h⁻¹) {M M' : ℕ} (hMM' : M ≤ M') :
    (h⁻¹) ^ M ≤ (h⁻¹) ^ M' := by
  -- `pow_le_pow_of_le_left` needs `0 ≤ h⁻¹`; that follows from `1 ≤ h⁻¹`.
  have h0 : 0 ≤ h⁻¹ := le_trans (by linarith) h1
  exact pow_le_pow_right₀ h1 hMM' -- pow_le_pow_of_le_left h0 h1 hMM'

set_option maxHeartbeats 800000 in
/-- Pointwise multiplication stability (Remark 3.3):

If `a ∈ S^{m₁}_λ` and `b ∈ S^{m₂}_λ`, then `(a*b) ∈ S^{m₁+m₂}_λ`.

The proof uses Leibniz formulas for `iteratedDeriv` in `τ` and in `t`, and the assumption
`h0 ≤ 1` to unify finitely many `(h⁻¹)^M` factors. -/
theorem mul
    (hh0 : h0 ≤ 1)
    (ha : SmLambda Y h0 m₁ a)
    (hb : SmLambda Y h0 m₂ b) :
    SmLambda Y h0 (m₁ + m₂) (fun h t τ => a h t τ * b h t τ) := by
  classical
  -- Smoothness in `(t, τ)` for fixed `h`.
  refine ⟨?_, ?_⟩
  · intro h
    exact (ha.1 h).mul (hb.1 h)
  -- Choose witnesses globally from the bounds.
  have ha_bound : ∀ α β : ℕ,
      ∃ C : ℝ, ∃ M : ℕ, 0 ≤ C ∧
        ∀ ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
          ∀ ⦃t : ℝ⦄, t ∈ Y →
            ∀ τ : ℝ,
              ‖dtdτ α β a h t τ‖ ≤ C * (h⁻¹) ^ M * japaneseBracket τ ^ (m₁ - (β : ℝ)) := ha.2
  have hb_bound : ∀ α β : ℕ,
      ∃ C : ℝ, ∃ M : ℕ, 0 ≤ C ∧
        ∀ ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
          ∀ ⦃t : ℝ⦄, t ∈ Y →
            ∀ τ : ℝ,
              ‖dtdτ α β b h t τ‖ ≤ C * (h⁻¹) ^ M * japaneseBracket τ ^ (m₂ - (β : ℝ)) := hb.2
  choose Ca Ma hA using ha_bound
  choose Cb Mb hB using hb_bound
  have hCa_nonneg : ∀ α β, 0 ≤ Ca α β := fun α β => (hA α β).1
  have hCb_nonneg : ∀ α β, 0 ≤ Cb α β := fun α β => (hB α β).1
  have hboundA :
      ∀ α β ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
        ∀ ⦃t : ℝ⦄, t ∈ Y →
          ∀ τ : ℝ,
            ‖dtdτ α β a h t τ‖ ≤ Ca α β * (h⁻¹) ^ Ma α β * (japaneseBracket τ) ^ (m₁ - (β : ℝ)) := by simp; aesop
  --  fun α β h hh t ht τ => (hA α β).2 h hh t ht τ
  have hboundB :
      ∀ α β ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
        ∀ ⦃t : ℝ⦄, t ∈ Y →
          ∀ τ : ℝ,
            ‖dtdτ α β b h t τ‖ ≤ Cb α β * (h⁻¹) ^ Mb α β * (japaneseBracket τ) ^ (m₂ - (β : ℝ)) := by simp; aesop
  --  fun α β h hh t ht τ => (hB α β).2 h hh t ht τ

  intro α β

  -- Double Leibniz index set: i ∈ [0..α], j ∈ [0..β].
  let I : Finset (ℕ × ℕ) :=
    (Finset.range (α + 1)).product (Finset.range (β + 1))

  -- Exponent for each term and the max exponent.
  let expo : (ℕ × ℕ) → ℕ := fun p => Ma p.1 p.2 + Mb (α - p.1) (β - p.2)
  let M : ℕ := I.sup expo

  -- Constant for each term and the sum constant.
  let constTerm : (ℕ × ℕ) → ℝ := fun p =>
    (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) * (Ca p.1 p.2) * (Cb (α - p.1) (β - p.2))
  let C : ℝ := I.sum constTerm

  refine ⟨C, M, ?_, ?_⟩
  · -- C ≥ 0
    refine Finset.sum_nonneg ?_
    intro p hp
    have hCa : 0 ≤ Ca p.1 p.2 := hCa_nonneg p.1 p.2
    have hCb : 0 ≤ Cb (α - p.1) (β - p.2) := hCb_nonneg (α - p.1) (β - p.2)
    have hchooseA : 0 ≤ (Nat.choose α p.1 : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hchooseB : 0 ≤ (Nat.choose β p.2 : ℝ) := by exact_mod_cast (Nat.zero_le _)
    --dsimp [constTerm]
    exact mul_nonneg (mul_nonneg (mul_nonneg hchooseA hchooseB) hCa) hCb
  · intro h hh t ht τ
    have h1 : (1 : ℝ) ≤ h⁻¹ := one_le_inv_of_mem_Ioc hh0 hh
    -- (or: by simpa using one_le_inv_of_mem_Ioc (h0 := h0) hh0 hh)

    -- (1) Leibniz expansion: `dtdτ α β (a*b)` equals a finite sum over `I`.
    have hLeib :
        dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ =
          ∑ p ∈ I,
            (Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              dtdτ p.1 p.2 a h t τ *
              dtdτ (α - p.1) (β - p.2) b h t τ := by
      -- This is the mixed Leibniz formula for `dtdτ`, proved above from the one-dimensional rule.
      simpa [I, mul_assoc, mul_left_comm, mul_comm] using
        (dtdτ_mul (a := a) (b := b) (h := h) (ha := ha.1 h) (hb := hb.1 h) α β t τ)

    -- (2) `‖Σ‖ ≤ Σ ‖·‖`.
    have hnorm_sum :
        ‖dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ‖ ≤
          ∑ p ∈ I,
            ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              dtdτ p.1 p.2 a h t τ *
              dtdτ (α - p.1) (β - p.2) b h t τ‖ := by
      simpa [hLeib] using (norm_sum_le I
        (fun p => (Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
          dtdτ p.1 p.2 a h t τ * dtdτ (α - p.1) (β - p.2) b h t τ))

    -- (3) Termwise bounds.
    have hterm :
        ∀ p ∈ I,
          ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              dtdτ p.1 p.2 a h t τ *
              dtdτ (α - p.1) (β - p.2) b h t τ‖
            ≤ constTerm p * (h⁻¹) ^ M * (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
      intro p hp
      -- i ≤ α, j ≤ β from membership.
      have hi : p.1 ≤ α := by
        have : p.1 ∈ Finset.range (α + 1) := (Finset.mem_product.1 hp).1
        exact Nat.le_of_lt_succ (Finset.mem_range.1 this)
      have hj : p.2 ≤ β := by
        have : p.2 ∈ Finset.range (β + 1) := (Finset.mem_product.1 hp).2
        exact Nat.le_of_lt_succ (Finset.mem_range.1 this)

      -- Bound on each derivative.
      have hAder := hboundA p.1 p.2 (h:=h) hh (t:=t) ht τ
      have hBder := hboundB (α - p.1) (β - p.2) (h:=h) hh (t:=t) ht τ

      -- Exponent control: expo p ≤ M (by definition of `sup`).
      have hexpo : expo p ≤ M := by
        exact Finset.le_sup (s:=I) (f:=expo) hp

      have hpow : (h⁻¹) ^ (expo p) ≤ (h⁻¹) ^ M :=
        pow_inv_mono_of_one_le (h:=h) h1 hexpo

      -- rpow algebra for the weight factor:
      -- ⟨τ⟩^(m₁-p.2) * ⟨τ⟩^(m₂-(β-p.2)) = ⟨τ⟩^((m₁+m₂)-β).
      have hbr_pos : 0 < japaneseBracket τ := japaneseBracket_pos τ
      have hnat : (p.2 + (β - p.2)) = β := Nat.add_sub_of_le hj
      have hcast : (p.2 : ℝ) + ((β - p.2 : ℕ) : ℝ) = (β : ℝ) := by
        exact_mod_cast hnat
      have hexp :
          (m₁ - (p.2 : ℝ)) + (m₂ - ((β - p.2 : ℕ) : ℝ)) = (m₁ + m₂) - (β : ℝ) := by
        -- elementary ring arithmetic using `hcast`
        nlinarith [hcast]
      have hweight :
          (japaneseBracket τ) ^ (m₁ - (p.2 : ℝ)) *
              (japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ))
            = (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
        -- `Real.rpow_add` gives `x^(a+b) = x^a * x^b` for `x > 0`.
        -- Use symmetry to match product form.
        have := (Real.rpow_add hbr_pos (m₁ - (p.2 : ℝ)) (m₂ - ((β - p.2 : ℕ) : ℝ))).symm
        -- Replace exponent sum using `hexp`.
        simpa [hexp, mul_assoc, mul_left_comm, mul_comm] using this

      -- Norm factorization:
      -- In ℂ, `‖x*y‖ = ‖x‖*‖y‖` and `‖(n:ℂ)‖ = n`.
      have hnorm_chooseA : ‖(Nat.choose α p.1 : ℂ)‖ = (Nat.choose α p.1 : ℝ) := by simp
      have hnorm_chooseB : ‖(Nat.choose β p.2 : ℂ)‖ = (Nat.choose β p.2 : ℝ) := by simp

      -- Start the estimate.
      calc
        ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              dtdτ p.1 p.2 a h t τ *
              dtdτ (α - p.1) (β - p.2) b h t τ‖
            = (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) *
                ‖dtdτ p.1 p.2 a h t τ‖ *
                ‖dtdτ (α - p.1) (β - p.2) b h t τ‖ := by
              -- normalize and use `norm_mul` repeatedly
              simp [mul_assoc]
        _ ≤ (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) *
              (Ca p.1 p.2 * (h⁻¹) ^ (Ma p.1 p.2) * (japaneseBracket τ) ^ (m₁ - (p.2 : ℝ))) *
              (Cb (α - p.1) (β - p.2) * (h⁻¹) ^ (Mb (α - p.1) (β - p.2)) *
                (japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ))) := by
              -- apply `hAder` and `hBder` inside the product, using monotonicity
              have hA0 :
                  0 ≤ Ca p.1 p.2 * (h⁻¹) ^ (Ma p.1 p.2) *
                        (japaneseBracket τ) ^ (m₁ - (p.2 : ℝ)) := by
                have hhpos : 0 < h := (Set.mem_Ioc.1 hh).1
                have hinv_nonneg : (0 : ℝ) ≤ h⁻¹ := inv_nonneg.2 (le_of_lt hhpos)
                have hpow_nonneg : (0 : ℝ) ≤ (h⁻¹) ^ (Ma p.1 p.2) := pow_nonneg hinv_nonneg _
                have hbr_nonneg :
                    (0 : ℝ) ≤ (japaneseBracket τ) ^ (m₁ - (p.2 : ℝ)) := by
                  exact Real.rpow_nonneg (japaneseBracket_nonneg τ) _
                -- `mul_nonneg` is more robust than `nlinarith` for nonlinear products.
                have hCa' : 0 ≤ Ca p.1 p.2 := hCa_nonneg p.1 p.2
                -- `Ca * (h⁻¹)^M` is nonnegative, and so is the Japanese bracket weight.
                -- Reassociate to match the goal shape.
                simpa [mul_assoc] using (mul_nonneg (mul_nonneg hCa' hpow_nonneg) hbr_nonneg)
              have hB0 :
                  0 ≤ Cb (α - p.1) (β - p.2) * (h⁻¹) ^ (Mb (α - p.1) (β - p.2)) *
                        (japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ)) := by
                have hhpos : 0 < h := (Set.mem_Ioc.1 hh).1
                have hinv_nonneg : (0 : ℝ) ≤ h⁻¹ := inv_nonneg.2 (le_of_lt hhpos)
                have hpow_nonneg :
                    (0 : ℝ) ≤ (h⁻¹) ^ (Mb (α - p.1) (β - p.2)) := pow_nonneg hinv_nonneg _
                have hbr_nonneg :
                    (0 : ℝ) ≤ (japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ)) := by
                  exact Real.rpow_nonneg (japaneseBracket_nonneg τ) _
                have hCb' : 0 ≤ Cb (α - p.1) (β - p.2) := hCb_nonneg (α - p.1) (β - p.2)
                simpa [mul_assoc] using (mul_nonneg (mul_nonneg hCb' hpow_nonneg) hbr_nonneg)
              -- now monotonicity in each factor
              have hchooseA : 0 ≤ (Nat.choose α p.1 : ℝ) := by
                exact_mod_cast (Nat.zero_le _)
              have hchooseB : 0 ≤ (Nat.choose β p.2 : ℝ) := by
                exact_mod_cast (Nat.zero_le _)
              have hchooseAB :
                  0 ≤ (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) :=
                mul_nonneg hchooseA hchooseB
              have hmul_norm :
                  ‖dtdτ p.1 p.2 a h t τ‖ * ‖dtdτ (α - p.1) (β - p.2) b h t τ‖
                    ≤
                    (Ca p.1 p.2 * (h⁻¹) ^ (Ma p.1 p.2) *
                        (japaneseBracket τ) ^ (m₁ - (p.2 : ℝ))) *
                      (Cb (α - p.1) (β - p.2) * (h⁻¹) ^ (Mb (α - p.1) (β - p.2)) *
                        (japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ))) :=
                mul_le_mul hAder hBder (norm_nonneg _) hA0
              have hmul_total :=
                mul_le_mul_of_nonneg_left hmul_norm hchooseAB
              -- reassociate to match the goal shape
              simpa [mul_assoc] using hmul_total
        _ = constTerm p * (h⁻¹) ^ (expo p) *
              (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
              -- rearrange; use `hweight` and `pow_add`
              dsimp [constTerm, expo]
              have hpows :
                  (h⁻¹) ^ (Ma p.1 p.2) * (h⁻¹) ^ (Mb (α - p.1) (β - p.2)) =
                    (h⁻¹) ^ (Ma p.1 p.2 + Mb (α - p.1) (β - p.2)) := by
                simpa using
                  (pow_add (h⁻¹) (Ma p.1 p.2) (Mb (α - p.1) (β - p.2))).symm
              -- `simp` can now reorder the commutative product, rewrite powers, and apply `hweight`.
              simp [mul_assoc, mul_left_comm, mul_comm, hweight]
              grind
        _ ≤ constTerm p * (h⁻¹) ^ M *
              (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
              -- replace `(h⁻¹)^(expo p)` by `(h⁻¹)^M` using monotonicity and nonnegativity
              have hct_nonneg : 0 ≤ constTerm p := by
                have hCa : 0 ≤ Ca p.1 p.2 := hCa_nonneg p.1 p.2
                have hCb : 0 ≤ Cb (α - p.1) (β - p.2) := hCb_nonneg (α - p.1) (β - p.2)
                have hchooseA : 0 ≤ (Nat.choose α p.1 : ℝ) := by exact_mod_cast (Nat.zero_le _)
                have hchooseB : 0 ≤ (Nat.choose β p.2 : ℝ) := by exact_mod_cast (Nat.zero_le _)
                dsimp [constTerm]
                exact mul_nonneg (mul_nonneg (mul_nonneg hchooseA hchooseB) hCa) hCb
              have hwt_nonneg :
                  0 ≤ (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
                exact Real.rpow_nonneg (japaneseBracket_nonneg τ) _
              -- `0 ≤ constTerm p` and `0 ≤ weight` allow multiplication of inequalities.
              have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hct_nonneg hwt_nonneg)
              -- rearrange
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ = constTerm p * (h⁻¹) ^ M * (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
              simp [mul_assoc]

    -- (4) Sum the termwise bounds and factor out the common term.
    have hsum :
        (∑ p ∈ I,
          ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              dtdτ p.1 p.2 a h t τ *
              dtdτ (α - p.1) (β - p.2) b h t τ‖)
        ≤ C * (h⁻¹) ^ M * (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
      -- Start from the termwise bound.
      have hsum₁ := Finset.sum_le_sum (fun p hp => hterm p hp)
      -- Factor out the common multiplier using `Finset.sum_mul`.
      -- `simp` in `hterm` has rewritten `(h⁻¹)^M` as `(h^M)⁻¹`, so we match that shape here.
      let w : ℝ := (h ^ M)⁻¹ * (japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ))
      have hfactor :
          (∑ p ∈ I, constTerm p * w) = (∑ p ∈ I, constTerm p) * w := by
        -- `Finset.sum_mul` is oriented as `(∑ f) * w = ∑ (f * w)`.
        simpa [w, mul_assoc] using (Finset.sum_mul I (fun p => constTerm p) w).symm
      -- Put it together.
      have : (∑ p ∈ I, ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              dtdτ p.1 p.2 a h t τ *
              dtdτ (α - p.1) (β - p.2) b h t τ‖)
            ≤ (∑ p ∈ I, constTerm p) * w := by
        -- rewrite the RHS of `hsum₁` into `(∑ constTerm) * w`
        -- (also reassociate the `constTerm p * w` that appears in `hsum₁`)
        simpa [w, hfactor, mul_assoc] using hsum₁
      -- finally unfold `C` and reassociate
      simpa [C, w, mul_assoc] using this

    -- (5) Conclude.
    exact le_trans hnorm_sum hsum

end SmLambda

end TwoChartEgorov
