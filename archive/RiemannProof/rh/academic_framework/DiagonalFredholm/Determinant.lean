import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Fredholm Determinants for Diagonal Operators

This file defines the regularized Fredholm determinant and proves key results
about when it vanishes.

## Main definitions

* `fredholm_det2` - The regularized determinant det₂(I - T)

## Main results

* `fredholm_det2_diagonal` - Product formula for diagonal operators
* `det_zero_iff_eigenvalue_one` - det(I - T) = 0 iff 1 is an eigenvalue
* `fredholm_det2_ne_zero_of_summable` - Determinant is nonzero if no eigenvalue equals 1
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology

variable {ι : Type*} [Countable ι]

/-- The regularized Fredholm determinant det₂(I - T) -/
noncomputable def fredholm_det2 (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) : ℂ :=
  ∏' i : ι, (1 - eigenvals i) * exp (eigenvals i)

/-- The regularized determinant formula -/
theorem fredholm_det2_diagonal (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  fredholm_det2 eigenvals h_bounded h_summable = ∏' i : ι, (1 - eigenvals i) * exp (eigenvals i) := by
  -- This is the definition
  rfl

/-- The determinant is zero iff 1 is an eigenvalue -/
theorem det_zero_iff_eigenvalue_one (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  fredholm_det2 eigenvals h_bounded h_summable = 0 ↔ ∃ i, eigenvals i = 1 := by
  simp only [fredholm_det2]
  -- The product is zero iff one of the factors is zero
  -- Since exp is never zero, this happens iff 1 - eigenvals i = 0 for some i
  have h_exp_ne_zero : ∀ i, exp (eigenvals i) ≠ 0 := fun i => exp_ne_zero _

  constructor
  · -- If product is zero, then some factor is zero
    intro h_prod_zero
    -- The product ∏' i, (1 - eigenvals i) * exp(eigenvals i) = 0
    -- First show the product is multipliable
    have h_mult : Multipliable (fun i => (1 - eigenvals i) * exp (eigenvals i)) := by
      -- Factor as product of two multipliable functions
      have h1 : Multipliable (fun i => 1 - eigenvals i) :=
        multipliable_one_sub_of_summable eigenvals h_summable
      have h2 : Multipliable (fun i => exp (eigenvals i)) := by
        -- exp is always positive and bounded, so multipliable when eigenvals summable
        -- Use that |exp(z)| = exp(Re(z)) and exp is bounded on bounded sets
        apply Multipliable.of_norm
        obtain ⟨C, hC⟩ := h_bounded
        -- For bounded eigenvals, exp(eigenvals) is bounded
        use Real.exp C
        intro i
        rw [norm_exp]
        exact Real.exp_le_exp_of_le (le_trans (Complex.abs_re_le_abs _) (hC i))
      convert Multipliable.mul h1 h2
      ext i
      rfl

    -- For a multipliable product to be zero, at least one factor must be zero
    obtain ⟨j, hj⟩ := Multipliable.eq_zero_iff h_mult |>.mp h_prod_zero
    -- So (1 - eigenvals j) * exp(eigenvals j) = 0
    -- Since exp(eigenvals j) ≠ 0, we must have 1 - eigenvals j = 0
    have : 1 - eigenvals j = 0 := by
      rw [mul_eq_zero] at hj
      cases hj with
      | inl h => exact h
      | inr h => exact (h_exp_ne_zero j h).elim
    -- Therefore eigenvals j = 1
    use j
    linarith

  · -- If eigenvals i = 1 for some i, then product is zero
    intro ⟨i, hi⟩
    -- We have eigenvals i = 1, so 1 - eigenvals i = 0
    -- Therefore (1 - eigenvals i) * exp(eigenvals i) = 0 * exp(eigenvals i) = 0
    -- So the i-th factor is zero, making the whole product zero

    -- First show the product is multipliable
    have h_mult : Multipliable (fun i => (1 - eigenvals i) * exp (eigenvals i)) := by
      -- Same as above
      have h1 : Multipliable (fun i => 1 - eigenvals i) :=
        multipliable_one_sub_of_summable eigenvals h_summable
      have h2 : Multipliable (fun i => exp (eigenvals i)) := by
        -- Same proof as above
        apply Multipliable.of_norm
        obtain ⟨C, hC⟩ := h_bounded
        use Real.exp C
        intro i
        rw [norm_exp]
        exact Real.exp_le_exp_of_le (le_trans (Complex.abs_re_le_abs _) (hC i))
      convert Multipliable.mul h1 h2
      ext i
      rfl

    -- Apply that if a factor is zero, the product is zero
    apply Multipliable.eq_zero_iff h_mult |>.mpr
    use i
    rw [hi]
    simp

/-- For trace-class diagonal operators, Fredholm det = standard det -/
theorem fredholm_det2_ne_zero_of_summable (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖))
  (h_no_one : ∀ i, eigenvals i ≠ 1) :
  fredholm_det2 eigenvals h_bounded h_summable ≠ 0 := by
  -- Use the previous theorem
  rw [det_zero_iff_eigenvalue_one eigenvals h_bounded h_summable]
  -- We need to show ¬(∃ i, eigenvals i = 1)
  -- But h_no_one says ∀ i, eigenvals i ≠ 1
  push_neg
  exact h_no_one

end AcademicRH.DiagonalFredholm
