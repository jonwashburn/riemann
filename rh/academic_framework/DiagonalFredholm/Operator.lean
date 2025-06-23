import rh.academic_framework.Core
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Diagonal Operators on ℓ²

This file defines diagonal operators on ℓ² spaces and proves their basic properties.

## Main definitions

* `DiagonalOperator` - A diagonal operator with given eigenvalues

## Main results

* `DiagonalOperator_apply` - Diagonal operators act by pointwise multiplication
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology

variable {ι : Type*} [Countable ι]

/-- A diagonal operator on ℓ² -/
noncomputable def DiagonalOperator (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C) :
  lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  -- First define the linear map
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 := {
    toFun := fun ψ =>
      ⟨fun i => eigenvals i * ψ i, by
        -- Show Memℓp for the result
        obtain ⟨C, hC⟩ := h_bounded
        -- Need to show this is in lp 2
        -- i.e., we need Summable fun i => ‖eigenvals i * ψ i‖^2
        have h_sq_summable : Summable fun i => ‖eigenvals i * ψ i‖^2 := by
          -- ‖eigenvals i * ψ i‖^2 = ‖eigenvals i‖^2 * ‖ψ i‖^2
          have h_eq : (fun i => ‖eigenvals i * ψ i‖^2) = fun i => ‖eigenvals i‖^2 * ‖ψ i‖^2 := by
            ext i
            rw [norm_mul, mul_pow]
          rw [h_eq]
          -- Since ‖eigenvals i‖ ≤ C, we have ‖eigenvals i‖^2 ≤ C^2
          have h_bound : ∀ i, ‖eigenvals i‖^2 * ‖ψ i‖^2 ≤ C^2 * ‖ψ i‖^2 := by
            intro i
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
          -- Apply comparison test
          apply Summable.of_nonneg_of_le
          · intro i; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
          · exact h_bound
          · exact Summable.mul_left _ ψ.property
        -- Convert to the required form
        simp only [← sq, Memℓp, lp.mem_ℓp_iff_summable_norm_rpow]
        norm_num
        exact h_sq_summable⟩,
    map_add' := by
      intro ψ φ
      ext i
      simp only [lp.coeFn_add, Pi.add_apply]
      ring
    map_smul' := by
      intro c ψ
      ext i
      simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
      simp only [smul_eq_mul]
      ring
  }
  -- Prove continuity
  have h_cont : ∃ C, ∀ ψ, ‖L ψ‖ ≤ C * ‖ψ‖ := by
    obtain ⟨C, hC⟩ := h_bounded
    use C
    intro ψ
    -- Need to show ‖L ψ‖ ≤ C * ‖ψ‖
    -- For lp 2 norm: ‖L ψ‖² = ∑ |eigenvals i * ψ i|²
    -- We have |eigenvals i * ψ i|² ≤ C² |ψ i|²
    -- So ‖L ψ‖² ≤ C² ∑ |ψ i|² = C² ‖ψ‖²
    -- Taking square roots: ‖L ψ‖ ≤ C ‖ψ‖

    -- First, compute ‖L ψ‖²
    have h_norm_sq : ‖L ψ‖^2 = ∑' i, ‖eigenvals i * ψ i‖^2 := by
      -- Use the fact that for lp 2, the norm squared is the sum of component norms squared
      rw [pow_two, ← lp.norm_sq_eq_inner_self]
      rw [lp.inner_def]
      simp [RCLike.inner_apply, conj_mul']
      congr 1
      ext i
      rw [norm_sq_eq_self]

    -- Bound each term
    have h_bound : ∑' i, ‖eigenvals i * ψ i‖^2 ≤ ∑' i, C^2 * ‖ψ i‖^2 := by
      apply tsum_le_tsum
      · intro i
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
      · exact Summable.mul_left _ ψ.property
      · have : Summable fun i => ‖eigenvals i * ψ i‖^2 := by
          apply Summable.of_nonneg_of_le
          · intro i; exact sq_nonneg _
          · intro i
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
          · exact Summable.mul_left _ ψ.property
        exact this

    -- Combine
    rw [h_norm_sq]
    have h_factor : ∑' i, C^2 * ‖ψ i‖^2 = C^2 * ∑' i, ‖ψ i‖^2 := by
      rw [← tsum_mul_left]
    rw [← h_factor] at h_bound
    -- We have ‖L ψ‖² ≤ C² * ∑' i, ‖ψ i‖²
    -- And ∑' i, ‖ψ i‖² = ‖ψ‖² (by definition of lp 2 norm)
    have h_ψ_norm : ∑' i, ‖ψ i‖^2 = ‖ψ‖^2 := by
      rw [pow_two, ← lp.norm_sq_eq_inner_self]
      rw [lp.inner_def]
      simp [RCLike.inner_apply, conj_mul']
      congr 1
      ext i
      rw [norm_sq_eq_self]
    rw [h_ψ_norm] at h_bound
    -- Take square roots
    have h_sqrt : Real.sqrt (‖L ψ‖^2) ≤ Real.sqrt (C^2 * ‖ψ‖^2) := by
      exact Real.sqrt_le_sqrt h_bound
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (norm_nonneg _),
        Real.sqrt_sq (norm_nonneg _)] at h_sqrt
    exact h_sqrt
  -- Use mkContinuousOfExistsBound
  exact L.mkContinuousOfExistsBound h_cont

/-- Diagonal operators act by pointwise multiplication -/
lemma DiagonalOperator_apply (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (ψ : lp (fun _ : ι => ℂ) 2) :
  DiagonalOperator eigenvals h_bounded ψ =
    ⟨fun i => eigenvals i * ψ i, by
      -- Same proof as in the definition
      obtain ⟨C, hC⟩ := h_bounded
      -- Need to show this is in lp 2
      -- i.e., we need Summable fun i => ‖eigenvals i * ψ i‖^2
      have h_sq_summable : Summable fun i => ‖eigenvals i * ψ i‖^2 := by
        -- ‖eigenvals i * ψ i‖^2 = ‖eigenvals i‖^2 * ‖ψ i‖^2
        have h_eq : (fun i => ‖eigenvals i * ψ i‖^2) = fun i => ‖eigenvals i‖^2 * ‖ψ i‖^2 := by
          ext i
          rw [norm_mul, mul_pow]
        rw [h_eq]
        -- Since ‖eigenvals i‖ ≤ C, we have ‖eigenvals i‖^2 ≤ C^2
        have h_bound : ∀ i, ‖eigenvals i‖^2 * ‖ψ i‖^2 ≤ C^2 * ‖ψ i‖^2 := by
          intro i
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
        -- Apply comparison test
        apply Summable.of_nonneg_of_le
        · intro i; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
        · exact h_bound
        · exact Summable.mul_left _ ψ.property
        -- Convert to the required form
        simp only [← sq, Memℓp, lp.mem_ℓp_iff_summable_norm_rpow]
        norm_num
        exact h_sq_summable⟩ := by
  -- This follows from the definition
  simp only [DiagonalOperator, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  -- The Memℓp proofs are equal because they're propositions
  rfl

/-- Helper: summable implies bounded for countable sets -/
lemma summable_implies_bounded (eigenvals : ι → ℂ)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  ∃ C, ∀ i, ‖eigenvals i‖ ≤ C := by
  -- If ∑‖eigenvals i‖ < ∞, then eigenvals i → 0, so they're bounded
  -- Standard argument: either finitely many terms are ≥ 1, or all are < 1
  -- In first case, max of those finite terms plus 1 works as bound
  -- In second case, 1 works as bound
  by_cases h : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C
  · exact h
  · -- If unbounded, we get a contradiction with summability
    push_neg at h
    -- h says: for all C, there exists i with ‖eigenvals i‖ > C
    -- This contradicts summability since summable sequences are bounded
    exfalso
    -- For any summable sequence, the terms must tend to 0
    have h_tendsto : Tendsto (fun i => ‖eigenvals i‖) cofinite (𝓝 0) := by
      exact h_summable.tendsto_cofinite_zero
    -- Therefore the sequence is eventually bounded by 1
    have h_eventually_bounded : ∀ᶠ i in cofinite, ‖eigenvals i‖ < 1 := by
      exact tendsto_nhds_metric.mp h_tendsto 1 (by norm_num)
    -- This means there's a finite set S such that for all i ∉ S, ‖eigenvals i‖ < 1
    obtain ⟨S, hS⟩ := eventually_cofinite.mp h_eventually_bounded
    -- The maximum of the finite set S plus 1 gives a bound
    let C := (S.image (fun i => ‖eigenvals i‖)).max' (by simp) + 1
    -- But h says no such bound exists, contradiction
    specialize h C
    obtain ⟨i, hi⟩ := h
    by_cases hi_in : i ∈ S
    · -- If i ∈ S, then ‖eigenvals i‖ ≤ max(S) < C
      have : ‖eigenvals i‖ ≤ (S.image (fun j => ‖eigenvals j‖)).max' (by simp) := by
        apply Finset.le_max'
        exact Finset.mem_image.mpr ⟨i, hi_in, rfl⟩
      linarith
    · -- If i ∉ S, then ‖eigenvals i‖ < 1 < C
      have : ‖eigenvals i‖ < 1 := hS i hi_in
      linarith

end AcademicRH.DiagonalFredholm
