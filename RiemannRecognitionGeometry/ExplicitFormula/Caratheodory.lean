/-
Copyright (c) 2025 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib

/-!
# Carathéodory Theory: Positive Kernels from Positive Real Part

This file proves Carathéodory's theorem: if F is holomorphic on the unit disk with
`Re F ≥ 0`, then the Carathéodory kernel

  `K_F(z,w) = (F(z) + conj(F(w))) / (1 - z·conj(w))`

is positive definite.

## Main results

* `szegoKernel_positive_definite`: The Szegő kernel is positive definite.
* `caratheodoryKernel_const_positive`: Constant functions give positive kernels.
* `eval_kernel_positive`: Point evaluation kernels are positive.
* `caratheodory_positive_definite`: The main theorem (requires the Herglotz representation hypothesis).

## References

* Carathéodory, C. (1911). Über den Variabilitätsbereich der Koeffizienten von Potenzreihen
* Herglotz, G. (1911). Über Potenzreihen mit positivem, reellen Teil im Einheitskreis
-/

noncomputable section

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace Caratheodory

/-!
## Positive Definite Kernels
-/

/-- A kernel is positive semidefinite on a set S. -/
def IsPositiveDefiniteKernelOn {α : Type*} (K : α → α → ℂ) (S : Set α) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α) (_hx : ∀ i, x i ∈ S) (c : Fin n → ℂ),
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, c i * starRingEnd ℂ (c j) * K (x i) (x j)).re

/-!
## The Szegő Kernel
-/

/-- The Szegő kernel: reproducing kernel of H². -/
def szegoKernel (z w : ℂ) : ℂ :=
  1 / (1 - z * starRingEnd ℂ w)

/-- The unit disk. -/
def unitDisk : Set ℂ := {z : ℂ | norm z < 1}

/-- For z, w in the disk, |z·conj(w)| < 1. -/
lemma abs_mul_conj_lt_one {z w : ℂ} (hz : norm z < 1) (hw : norm w < 1) :
    norm (z * starRingEnd ℂ w) < 1 := by
  calc norm (z * starRingEnd ℂ w)
      = norm z * norm (starRingEnd ℂ w) := by exact Complex.norm_mul z ((starRingEnd ℂ) w)
    _ = norm z * norm w := by rw [Complex.norm_conj]
    _ < 1 * 1 := by nlinarith [Complex.norm_of_nonneg z, Complex.abs.nonneg w]
    _ = 1 := by ring

/-- For z, w in the disk, 1 - z·conj(w) ≠ 0. -/
lemma one_sub_mul_conj_ne_zero {z w : ℂ} (hz : norm z < 1) (hw : norm w < 1) :
    1 - z * starRingEnd ℂ w ≠ 0 := by
  intro h
  have habs : norm (z * starRingEnd ℂ w) < 1 := abs_mul_conj_lt_one hz hw
  have heq : z * starRingEnd ℂ w = 1 := by
    have hsub : (1 : ℂ) - z * starRingEnd ℂ w = 0 := h
    calc z * starRingEnd ℂ w = 1 - (1 - z * starRingEnd ℂ w) := by ring
      _ = 1 - 0 := by rw [hsub]
      _ = 1 := by ring
  rw [heq] at habs; (expose_names; rw [← heq] at habs)
  aesop

/-- z * conj(z) = |z|² as a complex number. -/
lemma mul_conj_eq_normSq (z : ℂ) : z * starRingEnd ℂ z = (Complex.normSq z : ℂ) :=
  Complex.mul_conj z

/-- The power kernel (z·conj(w))^n is positive definite. -/
lemma power_kernel_positive_definite (n : ℕ) :
    IsPositiveDefiniteKernelOn (fun z w => (z * starRingEnd ℂ w) ^ n) unitDisk := by
  intro m x _hx c
  let s := ∑ i : Fin m, c i * (x i) ^ n
  have h : ∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ n =
      s * starRingEnd ℂ s := by
    simp only [mul_pow]
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show c i * starRingEnd ℂ (c j) * ((x i) ^ n * (starRingEnd ℂ (x j)) ^ n) =
          (c i * (x i) ^ n) * starRingEnd ℂ (c j * (x j) ^ n) by
        simp only [map_mul, map_pow]; ring]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    simp only [s, map_sum]
  rw [h]
  have hsq : s * starRingEnd ℂ s = (Complex.normSq s : ℂ) := mul_conj_eq_normSq s
  rw [hsq]
  simp only [Complex.ofReal_re, Complex.normSq_nonneg]

/--
The Szegő kernel is positive definite on the unit disk.

**Mathematical proof**:
S(z,w) = 1/(1 - z·w̄) = ∑_{k≥0} (z·w̄)^k (geometric series for |z·w̄| < 1)

The quadratic form:
∑_{i,j} c_i · c̄_j · S(x_i, x_j) = ∑_{i,j} c_i · c̄_j · ∑_k (x_i·x̄_j)^k
= ∑_k ∑_{i,j} c_i · c̄_j · (x_i·x̄_j)^k       (interchange sums)
= ∑_k |∑_i c_i · x_i^k|²                     (by power_kernel_positive_definite)
≥ 0                                          (sum of nonneg terms)
-/
theorem szegoKernel_positive_definite :
    IsPositiveDefiniteKernelOn szegoKernel unitDisk := by
  intro n x hx c
  by_cases hn : n = 0
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re, le_refl]
  -- Each power kernel term is nonneg
  have hpower : ∀ k : ℕ, 0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k).re :=
    fun k => power_kernel_positive_definite k n x hx c
  -- Convergence for each pair
  have hconv : ∀ i j : Fin n, norm (x i * starRingEnd ℂ (x j)) < 1 :=
    fun i j => abs_mul_conj_lt_one (hx i) (hx j)
  -- Szegő kernel equals geometric series
  have hszego_eq : ∀ i j : Fin n, szegoKernel (x i) (x j) =
      ∑' k : ℕ, (x i * starRingEnd ℂ (x j)) ^ k := by
    intro i j
    simp only [szegoKernel, one_div]
    have hnorm : ‖x i * starRingEnd ℂ (x j)‖ < 1 := by
      exact hconv i j
    exact (tsum_geometric_of_norm_lt_one hnorm).symm
  -- Summability of each geometric series
  have hSummable_geom : ∀ i j : Fin n, Summable (fun k => (x i * starRingEnd ℂ (x j)) ^ k) := by
    intro i j
    apply summable_geometric_of_norm_lt_one
    exact hconv i j
  -- Summability of scaled series
  have hSummable : ∀ i j : Fin n,
      Summable (fun k => c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k) := by
    intro i j
    exact (hSummable_geom i j).mul_left _
  -- The full quadratic form
  have hform : ∑ i : Fin n, ∑ j : Fin n, c i * starRingEnd ℂ (c j) * szegoKernel (x i) (x j) =
      ∑ i : Fin n, ∑ j : Fin n, c i * starRingEnd ℂ (c j) *
        ∑' k : ℕ, (x i * starRingEnd ℂ (x j)) ^ k := by
    congr 1; ext i; congr 1; ext j
    rw [hszego_eq i j]
  rw [hform]
  -- Distribute into tsum
  have hdistr : ∀ i j : Fin n, c i * starRingEnd ℂ (c j) *
      ∑' k : ℕ, (x i * starRingEnd ℂ (x j)) ^ k =
      ∑' k : ℕ, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k := by
    intro i j
    rw [tsum_mul_left]
  simp_rw [hdistr]
  -- Summability of inner sums
  have hSummable_j : ∀ i : Fin n, Summable (fun k => ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k) := by
    intro i
    exact summable_sum (fun j _ => hSummable i j)
  -- Summability of the full series
  have hSummable_all : Summable (fun k => ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k) := by
    exact summable_sum (fun i _ => hSummable_j i)
  -- Interchange finite sums with tsum
  have hinterchange : ∑ i : Fin n, ∑ j : Fin n,
      ∑' k : ℕ, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k =
      ∑' k : ℕ, ∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k := by
    have h1 : ∀ i : Fin n, ∑ j : Fin n,
        ∑' k : ℕ, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k =
        ∑' k : ℕ, ∑ j : Fin n,
          c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k := by
      intro i
      exact Eq.symm (Summable.tsum_finsetSum fun i_1 a ↦ hSummable i i_1)
    simp_rw [h1]
    aesop
  rw [hinterchange]
  -- Re of tsum = tsum of Re
  have hre_tsum : (∑' k : ℕ, ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k).re =
      ∑' k : ℕ, (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k).re :=
    Complex.re_tsum hSummable_all
  rw [hre_tsum]
  -- tsum of nonneg terms is nonneg
  exact tsum_nonneg hpower

/-!
## The Carathéodory Class
-/

/-- A function is holomorphic on the unit disk. -/
def IsHolomorphicOnDisk (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, norm z < 1 → DifferentiableAt ℂ F z

/-- A function is in the Carathéodory class. -/
structure IsCaratheodoryClass (F : ℂ → ℂ) : Prop where
  holomorphic : IsHolomorphicOnDisk F
  re_nonneg : ∀ z : ℂ, norm z < 1 → 0 ≤ (F z).re

/-- The Carathéodory kernel. -/
def caratheodoryKernel (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (F z + starRingEnd ℂ (F w)) / (1 - z * starRingEnd ℂ w)

/-!
## Herglotz Representation
-/

/-- The Herglotz kernel: H_ζ(z) = (ζ+z)/(ζ-z) for |ζ| = 1, |z| < 1. -/
def herglotzKernel (ζ z : ℂ) : ℂ := (ζ + z) / (ζ - z)

/-- A Herglotz representation. -/
structure HerglotzRepresentation (F : ℂ → ℂ) where
  μ : MeasureTheory.Measure ℂ
  finite : MeasureTheory.IsFiniteMeasure μ
  support : μ.restrict {z : ℂ | norm z = 1}ᶜ = 0
  c : ℝ
  representation : ∀ z : ℂ, norm z < 1 →
    F z = ∫ ζ : ℂ, herglotzKernel ζ z ∂μ + Complex.I * c

/-!
## Constant Function Case
-/

/-- c + conj(c) = 2 * Re(c) -/
lemma add_conj_eq_two_re (c : ℂ) : c + starRingEnd ℂ c = (2 * c.re : ℂ) := by
  apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

/-- For constant F = c, the kernel is 2·Re(c)·Szegő. -/
lemma caratheodoryKernel_const (c : ℂ) :
    ∀ z w : ℂ, caratheodoryKernel (fun _ => c) z w =
      (2 * c.re : ℂ) * szegoKernel z w := by
  intro z w
  simp only [caratheodoryKernel, szegoKernel]
  rw [add_conj_eq_two_re]
  ring

/-- Constant kernel is positive semidefinite. -/
theorem caratheodoryKernel_const_positive (c : ℂ) (hc : 0 ≤ c.re) :
    IsPositiveDefiniteKernelOn (caratheodoryKernel (fun _ => c)) unitDisk := by
  intro n x hx coeff
  simp_rw [caratheodoryKernel_const c]
  have hfactor : ∀ i j : Fin n,
      coeff i * starRingEnd ℂ (coeff j) * ((2 * c.re : ℂ) * szegoKernel (x i) (x j)) =
      (2 * c.re : ℂ) * (coeff i * starRingEnd ℂ (coeff j) * szegoKernel (x i) (x j)) := by
    intro i j; ring
  simp_rw [hfactor, ← Finset.mul_sum]
  have hszego := szegoKernel_positive_definite n x hx coeff
  have hscalar : 0 ≤ (2 * c.re : ℂ).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.re_ofNat, Complex.im_ofNat]
    linarith
  have him : (2 * c.re : ℂ).im = 0 := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.im_ofNat,
      mul_zero, zero_mul, add_zero]
  have hmul : ((2 * c.re : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
      coeff i * starRingEnd ℂ (coeff j) * szegoKernel (x i) (x j))).re =
      (2 * c.re : ℂ).re * (∑ i : Fin n, ∑ j : Fin n,
        coeff i * starRingEnd ℂ (coeff j) * szegoKernel (x i) (x j)).re := by
    simp only [Complex.mul_re, him, zero_mul, sub_zero]
  rw [hmul]
  exact mul_nonneg hscalar hszego

/-!
## Point Evaluation Kernel
-/

/-- The point evaluation kernel is positive semidefinite. -/
lemma eval_kernel_positive (ζ : ℂ) (_hζ : norm ζ = 1) :
    IsPositiveDefiniteKernelOn
      (fun z w => 1 / ((ζ - z) * (starRingEnd ℂ ζ - starRingEnd ℂ w))) unitDisk := by
  intro n x _hx c
  have hfactor : ∀ i j : Fin n,
      1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j))) =
      (1 / (ζ - x i)) * starRingEnd ℂ (1 / (ζ - x j)) := by
    intro i j
    simp only [map_div₀, map_one, map_sub]
    by_cases hne : (ζ - x i) = 0
    · simp only [hne, zero_mul, div_zero]
    · by_cases hne' : (ζ - x j) = 0
      · have hconj_zero : starRingEnd ℂ ζ - starRingEnd ℂ (x j) = 0 := by
          rw [← map_sub, hne', map_zero]
        simp only [hconj_zero, mul_zero, div_zero]
      · have hconj_ne : starRingEnd ℂ ζ - starRingEnd ℂ (x j) ≠ 0 := by
          intro h
          apply hne'
          have hstar : starRingEnd ℂ (ζ - x j) = 0 := by rw [map_sub]; exact h
          have hinj : Function.Injective (starRingEnd ℂ : ℂ → ℂ) := star_injective
          exact hinj (hstar.trans (map_zero (starRingEnd ℂ)).symm)
        field_simp [hne, hconj_ne]
  simp_rw [hfactor]
  let s := ∑ i : Fin n, c i * (1 / (ζ - x i))
  have h : ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * ((1 / (ζ - x i)) * starRingEnd ℂ (1 / (ζ - x j))) =
      s * starRingEnd ℂ s := by
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show c i * starRingEnd ℂ (c j) * ((1 / (ζ - x i)) * starRingEnd ℂ (1 / (ζ - x j))) =
          (c i * (1 / (ζ - x i))) * starRingEnd ℂ (c j * (1 / (ζ - x j))) by
        simp only [map_mul]; ring]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    simp only [s, map_sum]
  rw [h]
  have hsq : s * starRingEnd ℂ s = (Complex.normSq s : ℂ) := mul_conj_eq_normSq s
  rw [hsq]
  simp only [Complex.ofReal_re, Complex.normSq_nonneg]

/-!
## Herglotz-Carathéodory Connection
-/

/-- If |ζ| = 1, then normSq ζ = 1. -/
lemma normSq_eq_one_of_abs_eq_one {z : ℂ} (hz : norm z = 1) : Complex.normSq z = 1 := by
  have h := Complex.normSq_eq_abs z
  rw [hz] at h
  simp only [one_pow] at h
  exact h

/-- For |ζ| = 1, we have conj(ζ) = 1/ζ. -/
lemma conj_eq_inv_of_abs_eq_one {ζ : ℂ} (hζ : norm ζ = 1) :
    starRingEnd ℂ ζ = ζ⁻¹ := by
  have hnorm : Complex.normSq ζ = 1 := normSq_eq_one_of_abs_eq_one hζ
  -- z⁻¹ = conj z * (normSq z)⁻¹, so when normSq z = 1, z⁻¹ = conj z
  rw [Complex.inv_def, hnorm, inv_one, Complex.ofReal_one, mul_one]

/-- |ζ| = 1 implies ζ ≠ 0. -/
lemma ne_zero_of_abs_eq_one {ζ : ℂ} (hζ : norm ζ = 1) : ζ ≠ 0 := by
  intro h
  rw [h, Complex.abs.map_zero] at hζ
  exact one_ne_zero hζ.symm

/-- For |ζ| = 1 and |z| < 1, we have ζ - z ≠ 0. -/
lemma sub_ne_zero_of_circle_and_disk {ζ z : ℂ} (hζ : norm ζ = 1) (hz : norm z < 1) :
    ζ - z ≠ 0 := by
  intro h
  have heq : ζ = z := eq_of_sub_eq_zero h
  rw [← heq, hζ] at hz
  exact lt_irrefl 1 hz

/--
Key lemma: The Carathéodory kernel of the Herglotz function `H_ζ(z) = (ζ+z)/(ζ-z)`
equals twice the point evaluation kernel.

For |ζ| = 1, we have:
```
K_{H_ζ}(z,w) = (H_ζ(z) + conj(H_ζ(w))) / (1 - z·conj(w))
            = 2 / ((ζ-z)(conj(ζ)-conj(w)))
```

This is the key algebraic identity that connects Herglotz functions to point evaluation kernels.

The proof uses the fact that for |ζ| = 1, conj(ζ) = 1/ζ, so ζ · conj(ζ) = 1.
-/
lemma caratheodoryKernel_herglotz_eq_eval (ζ : ℂ) (hζ : norm ζ = 1)
    (z w : ℂ) (hz : norm z < 1) (hw : norm w < 1) :
    caratheodoryKernel (herglotzKernel ζ) z w =
      2 / ((ζ - z) * (starRingEnd ℂ ζ - starRingEnd ℂ w)) := by
  have hζ_ne : ζ ≠ 0 := ne_zero_of_abs_eq_one hζ
  have hz_ne : ζ - z ≠ 0 := sub_ne_zero_of_circle_and_disk hζ hz
  have hw_ne : ζ - w ≠ 0 := sub_ne_zero_of_circle_and_disk hζ hw
  have h1_ne : 1 - z * starRingEnd ℂ w ≠ 0 := one_sub_mul_conj_ne_zero hz hw
  have hζ_inv : starRingEnd ℂ ζ = ζ⁻¹ := conj_eq_inv_of_abs_eq_one hζ
  have hζζ_inv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ_ne
  have hconj_ne : ζ⁻¹ - starRingEnd ℂ w ≠ 0 := by
    rw [← hζ_inv, ← map_sub]
    intro h
    apply hw_ne
    exact star_injective (h.trans (star_zero ℂ).symm)
  have hζ_conj_ne : starRingEnd ℂ ζ - starRingEnd ℂ w ≠ 0 := by rw [hζ_inv]; exact hconj_ne
  simp only [caratheodoryKernel, herglotzKernel, map_div₀, map_add, map_sub]
  rw [hζ_inv]
  have hprod : (ζ - z) * (ζ⁻¹ - starRingEnd ℂ w) ≠ 0 := mul_ne_zero hz_ne hconj_ne
  -- Step 1: Show that the numerator (ζ+z)(ζ⁻¹-w̄) + (ζ⁻¹+w̄)(ζ-z) = 2(1 - zw̄)
  have hnumer : (ζ + z) * (ζ⁻¹ - starRingEnd ℂ w) + (ζ⁻¹ + starRingEnd ℂ w) * (ζ - z) =
      2 * (1 - z * starRingEnd ℂ w) := by
    -- Expand using ζ·ζ⁻¹ = 1
    calc (ζ + z) * (ζ⁻¹ - starRingEnd ℂ w) + (ζ⁻¹ + starRingEnd ℂ w) * (ζ - z)
        = ζ * ζ⁻¹ - ζ * starRingEnd ℂ w + z * ζ⁻¹ - z * starRingEnd ℂ w +
          (ζ⁻¹ * ζ - ζ⁻¹ * z + starRingEnd ℂ w * ζ - starRingEnd ℂ w * z) := by ring
      _ = 1 - ζ * starRingEnd ℂ w + z * ζ⁻¹ - z * starRingEnd ℂ w +
          (1 - ζ⁻¹ * z + starRingEnd ℂ w * ζ - starRingEnd ℂ w * z) := by
          rw [hζζ_inv, mul_comm ζ⁻¹ ζ, hζζ_inv]
      _ = 2 - 2 * z * starRingEnd ℂ w := by ring
      _ = 2 * (1 - z * starRingEnd ℂ w) := by ring
  -- Step 2: Combine the fractions
  -- LHS = ((ζ+z)/(ζ-z) + (ζ⁻¹+w̄)/(ζ⁻¹-w̄)) / (1 - z·w̄)
  --     = [(ζ+z)(ζ⁻¹-w̄) + (ζ⁻¹+w̄)(ζ-z)] / [(ζ-z)(ζ⁻¹-w̄)(1 - z·w̄)]
  --     = 2(1 - z·w̄) / [(ζ-z)(ζ⁻¹-w̄)(1 - z·w̄)]
  --     = 2 / [(ζ-z)(ζ⁻¹-w̄)]
  -- Note: div_add_div gives a + c·b in numerator, so we need to account for order
  have hnumer' : (ζ + z) * (ζ⁻¹ - starRingEnd ℂ w) + (ζ - z) * (ζ⁻¹ + starRingEnd ℂ w) =
      2 * (1 - z * starRingEnd ℂ w) := by
    have h := hnumer
    calc (ζ + z) * (ζ⁻¹ - starRingEnd ℂ w) + (ζ - z) * (ζ⁻¹ + starRingEnd ℂ w)
        = (ζ + z) * (ζ⁻¹ - starRingEnd ℂ w) + (ζ⁻¹ + starRingEnd ℂ w) * (ζ - z) := by ring
      _ = 2 * (1 - z * starRingEnd ℂ w) := hnumer
  have hstep : (ζ + z) / (ζ - z) + (ζ⁻¹ + starRingEnd ℂ w) / (ζ⁻¹ - starRingEnd ℂ w) =
      2 * (1 - z * starRingEnd ℂ w) / ((ζ - z) * (ζ⁻¹ - starRingEnd ℂ w)) := by
    rw [div_add_div _ _ hz_ne hconj_ne, hnumer']
  rw [hstep, div_div]
  -- Goal: 2*(1-zw̄) / ((ζ-z) * (ζ⁻¹-w̄) * (1-zw̄)) = 2 / ((ζ-z) * (ζ⁻¹-w̄))
  rw [mul_comm ((ζ - z) * (ζ⁻¹ - starRingEnd ℂ w)) (1 - z * starRingEnd ℂ w)]
  rw [mul_comm 2 (1 - z * starRingEnd ℂ w)]
  rw [mul_div_mul_left 2 ((ζ - z) * (ζ⁻¹ - starRingEnd ℂ w)) h1_ne]

/--
The Carathéodory kernel of a Herglotz function is positive semidefinite.

Since `K_{H_ζ} = 2 · (point evaluation kernel)` and point evaluation kernels
are positive definite (by `eval_kernel_positive`), this is immediate.

The proof relies on `caratheodoryKernel_herglotz_eq_eval` which shows:
  K_{H_ζ}(z,w) = 2 / ((ζ-z)(conj(ζ)-conj(w)))
-/
theorem caratheodoryKernel_herglotz_positive (ζ : ℂ) (hζ : norm ζ = 1) :
    IsPositiveDefiniteKernelOn (caratheodoryKernel (herglotzKernel ζ)) unitDisk := by
  intro n x hx c
  -- Step 1: Show that K_{H_ζ}(z,w) = 2 / ((ζ-z)(conj(ζ)-conj(w))) = 2 * (eval kernel)
  have hform : ∀ i j : Fin n,
      caratheodoryKernel (herglotzKernel ζ) (x i) (x j) =
        2 * (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))) := by
    intro i j
    rw [caratheodoryKernel_herglotz_eq_eval ζ hζ (x i) (x j) (hx i) (hx j)]
    ring
  -- Step 2: Factor out the 2 from the sum
  have hfactor : ∀ i j : Fin n,
      c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) =
      2 * (c i * starRingEnd ℂ (c j) * (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j))))) := by
    intro i j
    rw [hform i j]
    ring
  -- Turn the double sum into `2 * (eval-kernel quadratic form)` without expanding `re`.
  simp_rw [hfactor]
  let S : ℂ :=
    ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) *
        (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j))))
  have hS : 0 ≤ S.re := by
    -- this is exactly `eval_kernel_positive`
    simpa [S] using eval_kernel_positive ζ hζ n x hx c
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
        (2 : ℂ) *
          (c i * starRingEnd ℂ (c j) *
            (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))))) = (2 : ℂ) * S := by
    classical
    -- pull `2` out of the inner sum, then out of the outer sum
    have hinner :
        (∑ i : Fin n, ∑ j : Fin n,
            (2 : ℂ) *
              (c i * starRingEnd ℂ (c j) *
                (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))))) =
          ∑ i : Fin n, (2 : ℂ) * (∑ j : Fin n,
            c i * starRingEnd ℂ (c j) *
              (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j))))) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa [Finset.mul_sum] using
        (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
          (f := fun j =>
            c i * starRingEnd ℂ (c j) *
              (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))))
          (a := (2 : ℂ))).symm
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          (2 : ℂ) *
            (c i * starRingEnd ℂ (c j) *
              (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))))) =
          ∑ i : Fin n, (2 : ℂ) * (∑ j : Fin n,
            c i * starRingEnd ℂ (c j) *
              (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j))))) := hinner
      _ = (2 : ℂ) * S := by
        -- outer pull-out
        simp [S, Finset.mul_sum]
  -- finish: real part scales by `2` (a real scalar)
  have hre2 : ∀ z : ℂ, ((2 : ℂ) * z).re = 2 * z.re := by
    intro z
    simp [Complex.mul_re]
  -- Goal is `0 ≤ (∑∑ 2 * ...).re`. Rewrite the double sum to `(2:ℂ) * S` and use `hS`.
  have hreEq :
      ((∑ i : Fin n, ∑ j : Fin n,
          (2 : ℂ) *
            (c i * starRingEnd ℂ (c j) *
              (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))))) : ℂ).re
        =
      (((2 : ℂ) * S).re) := by
    simpa using congrArg Complex.re hsum
  -- `simp` knows `0 ≤ ((2:ℂ) * S).re` is equivalent to `0 ≤ S.re` since `2 > 0`.
  have h2S' : 0 ≤ ((2 : ℂ) * S).re := by
    -- rewrite to `0 ≤ 2 * S.re` and use `hS`
    have : 0 ≤ 2 * S.re := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS
    simpa [hre2] using this
  -- now close the goal
  -- (the goal is the LHS of `hreEq`)
  -- so we rewrite it to the RHS and apply `h2S'`.
  have : 0 ≤ ((∑ i : Fin n, ∑ j : Fin n,
          (2 : ℂ) *
            (c i * starRingEnd ℂ (c j) *
              (1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j)))))) : ℂ).re := by
    -- Rewrite the goal using `hreEq` and close with `h2S'`.
    -- We use `rw` so we don't let `simp` cancel the factor `2`.
    -- `hreEq` : (sum).re = ((2:ℂ) * S).re
    -- so `rw [hreEq]` turns the goal into `0 ≤ ((2:ℂ) * S).re`.
    rw [hreEq]
    exact h2S'
  simpa using this

/-!
## Main Theorem

The complete proof of Carathéodory's theorem requires the Herglotz representation theorem:
every holomorphic function F on the disk with Re(F) ≥ 0 can be written as

  F(z) = ∫_{|ζ|=1} (ζ+z)/(ζ-z) dμ(ζ) + i·Im(F(0))

for a positive finite measure μ on the unit circle with μ(circle) = Re(F(0)).

This is a fundamental result from classical complex analysis (Herglotz 1911),
but formalizing it completely requires:
1. Poisson integral representation for harmonic functions
2. Riesz representation theorem for positive linear functionals
3. Fatou's theorem for boundary values

We have proven all the key algebraic ingredients:
- szegoKernel_positive_definite: Szegő kernel is positive definite
- caratheodoryKernel_const_positive: constant functions give positive kernels
- eval_kernel_positive: point evaluation kernels are positive

Given the Herglotz representation, the main theorem follows by linearity:
the Carathéodory kernel factors as an integral of positive point kernels.
-/

/-!
## Herglotz Representation Theorem

This is a fundamental result from classical complex analysis (Herglotz 1911):
Every holomorphic function F on the unit disk with Re(F) ≥ 0 admits a representation
  F(z) = ∫_{|ζ|=1} (ζ+z)/(ζ-z) dμ(ζ) + i·Im(F(0))
for a unique positive finite measure μ on the unit circle.

### Key identity connecting Cauchy and Herglotz kernels:
For |ζ| = 1 and |z| < 1, the Cauchy kernel relates to the Herglotz kernel by:
  ζ/(ζ-z) = (H_ζ(z) + 1)/2  where H_ζ(z) = (ζ+z)/(ζ-z)

This identity is the bridge from Cauchy integral formula to Herglotz/Poisson representation.
-/

/-- The Cauchy-Herglotz identity: ζ/(ζ-z) = (1 + H_ζ(z))/2 for ζ ≠ z. -/
lemma cauchy_herglotz_identity {ζ z : ℂ} (hne : ζ - z ≠ 0) :
    ζ / (ζ - z) = (1 + herglotzKernel ζ z) / 2 := by
  simp only [herglotzKernel]
  field_simp
  ring

/-- The Herglotz kernel at z = 0 equals 1 (for any ζ ≠ 0). -/
lemma herglotzKernel_zero {ζ : ℂ} (hζ : ζ ≠ 0) : herglotzKernel ζ 0 = 1 := by
  simp only [herglotzKernel, add_zero, sub_zero]
  exact div_self hζ

/-- The Poisson kernel (real part of Herglotz) at z = 0 equals 1. -/
lemma poissonKernel_zero {ζ : ℂ} (hζ : norm ζ = 1) :
    (herglotzKernel ζ 0).re = 1 := by
  have hne : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    simp at hζ
  rw [herglotzKernel_zero hne]
  simp

/-!
### Proof outline (not yet formalized in Mathlib):
1. For 0 < r < 1, define measures μ_r := (1/2π) · Re F(r·e^{iθ}) dθ on the circle
2. These are positive measures with total mass Re F(0) (mean value property)
3. By Banach-Alaoglu (weak-* compactness), extract a subnet converging to measure μ
4. The Cauchy integral formula transforms to the Herglotz representation in the limit

The formalization would require foundational harmonic analysis not in Mathlib:
- Poisson integral representation for positive harmonic functions
- Riesz representation theorem for positive functionals on C(circle)
- Fatou's theorem for boundary values (or weak-* compactness arguments)

We record this as an explicit hypothesis (`Prop`) rather than a global Lean `axiom`.
This keeps the Route‑3 pipeline fully “no-axiom” in Lean, while isolating the remaining classical
analysis gap as a single named assumption to be proved later.
-/
def herglotz_representation (F : ℂ → ℂ) (_hF : IsCaratheodoryClass F) : Prop :=
  Nonempty (HerglotzRepresentation F)

/--
**Carathéodory's Theorem**: If F is holomorphic on the disk with Re(F) ≥ 0,
then the Carathéodory kernel is positive definite.

This theorem is proven modulo the Herglotz representation theorem.
All algebraic ingredients have been formally verified above.
-/
theorem caratheodory_positive_definite
    (F : ℂ → ℂ) (hF : IsCaratheodoryClass F)
    (hHerg : herglotz_representation F hF) :
    IsPositiveDefiniteKernelOn (caratheodoryKernel F) unitDisk := by
  intro n x hx c
  -- Get the Herglotz representation (as a hypothesis)
  rcases hHerg with ⟨rep⟩
  rcases rep with ⟨μ, _hfinite, _hsupport, _β, _hrep⟩
  -- The proof uses:
  -- 1. F(z) = ∫ (ζ+z)/(ζ-z) dμ + iβ by Herglotz representation
  -- 2. K_F(z,w) = ∫ K_{H_ζ}(z,w) dμ by linearity
  -- 3. Each K_{H_ζ} is positive definite (factors through eval_kernel_positive)
  -- 4. Integral of nonnegative function is nonnegative
  --
  -- The algebraic identity for step 3:
  -- For |ζ| = 1, the Carathéodory kernel of H_ζ(z) = (ζ+z)/(ζ-z) equals
  -- 2 / ((ζ-z)(conj(ζ)-conj(w))), which is 2 times the point evaluation kernel.
  --
  -- This follows from:
  -- H_ζ(z) + conj(H_ζ(w)) = (ζ+z)/(ζ-z) + (conj(ζ)+conj(w))/(conj(ζ)-conj(w))
  --                       = 2(1 - z·conj(w)) / ((ζ-z)(conj(ζ)-conj(w)))
  -- for |ζ| = 1 (using conj(ζ) = 1/ζ).
  --
  -- Dividing by (1 - z·conj(w)) gives:
  -- K_{H_ζ}(z,w) = 2 / ((ζ-z)(conj(ζ)-conj(w)))
  --
  -- The quadratic form then factors as:
  -- ∑_{i,j} c_i·conj(c_j)·K_F(x_i,x_j) = ∫ [∑_{i,j} c_i·conj(c_j)·K_{H_ζ}(x_i,x_j)] dμ
  --                                    = ∫ [2·|∑_i c_i/(ζ-x_i)|²] dμ ≥ 0
  --
  -- The full measure-theoretic argument requires:
  -- - Fubini for finite sums and integrals
  -- - Positivity of integral of nonnegative function
  -- - Handling the support condition (μ is on the unit circle)
  --
  -- We complete the proof using the established algebraic facts.
  classical
  letI : MeasureTheory.IsFiniteMeasure μ := _hfinite

  -- From support condition: μ-a.e. |ζ| = 1
  have hμcircle : ∀ᵐ ζ ∂μ, norm ζ = 1 := by
    have h0 : μ ({z : ℂ | norm z = 1}ᶜ) = 0 := by
      have := congrArg (fun ν : MeasureTheory.Measure ℂ => ν Set.univ) _hsupport
      simpa using this
    exact Filter.eventually_of_mem (MeasureTheory.mem_ae_iff.mpr h0) (fun _ h => h)

  -- The quadratic form for K_{H_ζ} is nonnegative on the unit circle
  let qH : ℂ → ℂ := fun ζ =>
    ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j)

  have hqH_nonneg : 0 ≤ᵐ[μ] fun ζ => (qH ζ).re := by
    filter_upwards [hμcircle] with ζ hζ
    exact caratheodoryKernel_herglotz_positive ζ hζ n x hx c

  -- The key step: K_F quadratic form equals ∫ qH dμ
  -- This follows from the Herglotz representation:
  -- F(z) = ∫ H_ζ(z) dμ + I·β, so K_F = ∫ K_{H_ζ} dμ (I·β terms cancel)
  -- Then Fubini swaps finite sums with integral.
  --
  -- Rather than prove this in full detail (which requires careful measure theory),
  -- we observe that the result is a direct consequence of:
  -- 1. The kernel decomposition K_F = ∫ K_{H_ζ} dμ
  -- 2. Fubini for finite sums
  -- 3. ∫ (nonneg) dμ ≥ 0
  --
  -- The algebraic work (steps 1-2) is routine given the Herglotz representation axiom.
  -- We complete the proof by showing the goal equals ∫ (qH ζ).re dμ ≥ 0.
  -- Integrability: on the unit circle (|ζ| = 1), for |x| < 1, the functions are bounded
  -- since |ζ - x| ≥ 1 - |x| > 0 keeps the denominator away from zero.

  -- Helper: AEStronglyMeasurable for herglotzKernel
  have hMeasH : ∀ i : Fin n,
      MeasureTheory.AEStronglyMeasurable (fun ζ => herglotzKernel ζ (x i)) μ := by
    intro i
    -- The function ζ ↦ (ζ + x_i)/(ζ - x_i) is measurable (rational function)
    simp only [herglotzKernel]
    apply Measurable.aestronglyMeasurable
    exact (measurable_id.add_const _).div (measurable_id.sub_const _)

  -- Step 1: H_ζ(x_i) = (ζ + x_i)/(ζ - x_i) is bounded on support
  have hIntH : ∀ i : Fin n, MeasureTheory.Integrable (fun ζ => herglotzKernel ζ (x i)) μ := by
    intro i
    -- On the unit circle: |H_ζ(x_i)| ≤ (1 + |x_i|)/(1 - |x_i|) which is finite
    have hxi_lt : norm (x i) < 1 := hx i
    have hdenom_pos : 0 < 1 - norm (x i) := by linarith
    let M := (1 + norm (x i)) / (1 - norm (x i))
    have hbound : ∀ᵐ ζ ∂μ, ‖herglotzKernel ζ (x i)‖ ≤ M := by
      filter_upwards [hμcircle] with ζ hζ
      simp only [herglotzKernel, norm_div]
      -- ‖ζ + x_i‖ ≤ ‖ζ‖ + ‖x_i‖ = 1 + |x_i|
      have hnum : ‖ζ + x i‖ ≤ 1 + norm (x i) := by
        calc ‖ζ + x i‖ ≤ ‖ζ‖ + ‖x i‖ := norm_add_le ζ (x i)
          _ = norm ζ + norm (x i) := by simp only [Complex.norm_eq_abs]
          _ = 1 + norm (x i) := by rw [hζ]
      -- ‖ζ - x_i‖ ≥ |‖ζ‖ - ‖x_i‖| ≥ 1 - |x_i|
      have hdenom : 1 - norm (x i) ≤ ‖ζ - x i‖ := by
        calc 1 - norm (x i)
            = norm ζ - norm (x i) := by rw [hζ]
          _ ≤ norm (ζ - x i) := AbsoluteValue.le_sub norm ζ (x i)
          _ = ‖ζ - x i‖ := by simp only [Complex.norm_eq_abs]
      have hζxi_ne : ζ - x i ≠ 0 := by
        intro h
        simp only [sub_eq_zero] at h
        rw [h] at hζ
        rw [hζ] at hxi_lt
        exact (lt_irrefl 1) hxi_lt
      have hdenom_pos' : 0 < ‖ζ - x i‖ := norm_pos_iff.mpr hζxi_ne
      calc ‖ζ + x i‖ / ‖ζ - x i‖ ≤ (1 + norm (x i)) / ‖ζ - x i‖ := by
            apply div_le_div_of_nonneg_right hnum (le_of_lt hdenom_pos')
        _ ≤ (1 + norm (x i)) / (1 - norm (x i)) := by
            have hpos : 0 ≤ 1 + norm (x i) := by positivity
            exact div_le_div_of_nonneg_left hpos hdenom_pos hdenom
    have htop : MeasureTheory.Memℒp (fun ζ => herglotzKernel ζ (x i)) ⊤ μ :=
      MeasureTheory.memℒp_top_of_bound (hMeasH i) M hbound
    exact htop.integrable le_top

  -- Step 2: conj(H_ζ(x_j)) is also integrable (same bound)
  have hIntHconj : ∀ j : Fin n,
      MeasureTheory.Integrable (fun ζ => starRingEnd ℂ (herglotzKernel ζ (x j))) μ := by
    intro j
    -- conj preserves norms, so same bound works
    have hxi_lt : norm (x j) < 1 := hx j
    have hdenom_pos : 0 < 1 - norm (x j) := by linarith
    let M := (1 + norm (x j)) / (1 - norm (x j))
    have hMeasConj : MeasureTheory.AEStronglyMeasurable
        (fun ζ => starRingEnd ℂ (herglotzKernel ζ (x j))) μ :=
      Complex.continuous_conj.comp_aestronglyMeasurable (hMeasH j)
    have hbound : ∀ᵐ ζ ∂μ, ‖starRingEnd ℂ (herglotzKernel ζ (x j))‖ ≤ M := by
      filter_upwards [hμcircle] with ζ hζ
      rw [Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
      simp only [herglotzKernel, norm_div]
      have hnum : ‖ζ + x j‖ ≤ 1 + norm (x j) := by
        calc ‖ζ + x j‖ ≤ ‖ζ‖ + ‖x j‖ := norm_add_le ζ (x j)
          _ = norm ζ + norm (x j) := by simp only [Complex.norm_eq_abs]
          _ = 1 + norm (x j) := by rw [hζ]
      have hdenom : 1 - norm (x j) ≤ ‖ζ - x j‖ := by
        calc 1 - norm (x j)
            = norm ζ - norm (x j) := by rw [hζ]
          _ ≤ norm (ζ - x j) := AbsoluteValue.le_sub norm ζ (x j)
          _ = ‖ζ - x j‖ := by simp only [Complex.norm_eq_abs]
      have hζxj_ne : ζ - x j ≠ 0 := by
        intro h
        simp only [sub_eq_zero] at h
        rw [h] at hζ
        rw [hζ] at hxi_lt
        exact (lt_irrefl 1) hxi_lt
      have hdenom_pos' : 0 < ‖ζ - x j‖ := norm_pos_iff.mpr hζxj_ne
      calc ‖ζ + x j‖ / ‖ζ - x j‖ ≤ (1 + norm (x j)) / ‖ζ - x j‖ := by
            apply div_le_div_of_nonneg_right hnum (le_of_lt hdenom_pos')
        _ ≤ (1 + norm (x j)) / (1 - norm (x j)) := by
            have hpos : 0 ≤ 1 + norm (x j) := by positivity
            exact div_le_div_of_nonneg_left hpos hdenom_pos hdenom
    have htop : MeasureTheory.Memℒp (fun ζ => starRingEnd ℂ (herglotzKernel ζ (x j))) ⊤ μ :=
      MeasureTheory.memℒp_top_of_bound hMeasConj M hbound
    exact htop.integrable le_top

  -- Step 3: K_{H_ζ}(x_i, x_j) is integrable (product of bounded functions, finite measure)
  have hIntK : ∀ i j : Fin n,
      MeasureTheory.Integrable (fun ζ => caratheodoryKernel (herglotzKernel ζ) (x i) (x j)) μ := by
    intro i j
    -- K_{H_ζ}(x_i, x_j) = (H_ζ(x_i) + conj(H_ζ(x_j))) / (1 - x_i·conj(x_j))
    -- The denominator is a nonzero constant, so dividing by it preserves integrability
    simp only [caratheodoryKernel]
    apply MeasureTheory.Integrable.div_const
    exact (hIntH i).add (hIntHconj j)

  -- Step 4: The kernel decomposition K_F(x_i,x_j) = ∫ K_{H_ζ}(x_i,x_j) dμ
  have hKernel : ∀ i j : Fin n,
      caratheodoryKernel F (x i) (x j) =
        ∫ ζ, caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ := by
    intro i j
    have hFi := _hrep (x i) (hx i)
    have hFj := _hrep (x j) (hx j)
    -- F(x_i) + conj(F(x_j)) using integral_conj
    have hNumer : F (x i) + starRingEnd ℂ (F (x j)) =
        (∫ ζ, herglotzKernel ζ (x i) ∂μ) +
        (∫ ζ, starRingEnd ℂ (herglotzKernel ζ (x j)) ∂μ) := by
      rw [hFi, hFj]
      -- conj(∫ f + I·β) = ∫ conj(f) + conj(I·β)
      have hconj : starRingEnd ℂ ((∫ ζ, herglotzKernel ζ (x j) ∂μ) + Complex.I * _β) =
          (∫ ζ, starRingEnd ℂ (herglotzKernel ζ (x j)) ∂μ) - Complex.I * _β := by
        simp only [map_add, map_mul]
        -- Use integral_conj: ∫ conj(f) = conj(∫ f)
        rw [integral_conj]
        simp [Complex.conj_I]
        ring
      rw [hconj]
      ring
    simp only [caratheodoryKernel]
    rw [hNumer]
    rw [← MeasureTheory.integral_add (hIntH i) (hIntHconj j)]
    have hIntSum : MeasureTheory.Integrable
        (fun ζ => herglotzKernel ζ (x i) + starRingEnd ℂ (herglotzKernel ζ (x j))) μ :=
      (hIntH i).add (hIntHconj j)
    -- Factor out constant denominator: (∫ f) / c = ∫ (f / c)
    rw [(MeasureTheory.integral_div _ _).symm]

  -- Step 5: The quadratic form equals the integral
  have hQuadEq : (∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * caratheodoryKernel F (x i) (x j)) =
      ∫ ζ, qH ζ ∂μ := by
    -- Rewrite each K_F term using hKernel
    have hStep1 : (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * caratheodoryKernel F (x i) (x j)) =
        (∑ i : Fin n, ∑ j : Fin n,
          c i * starRingEnd ℂ (c j) * ∫ ζ, caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ) := by
      congr 1
      ext i
      congr 1
      ext j
      rw [hKernel i j]
    rw [hStep1]
    -- Pull constants into integrals
    have hIntKc : ∀ i j : Fin n,
        MeasureTheory.Integrable
          (fun ζ => c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j)) μ :=
      fun i j => (hIntK i j).const_mul _
    have hStep2 : (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * ∫ ζ, caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ) =
        (∑ i : Fin n, ∑ j : Fin n,
          ∫ ζ, c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ) := by
      congr 1
      ext i
      congr 1
      ext j
      rw [← MeasureTheory.integral_mul_left]
    rw [hStep2]
    -- Use Fubini: ∑∑∫ = ∫∑∑
    -- First swap inner sum with integral: ∑_j ∫ = ∫ ∑_j
    have hStep3a : ∀ i : Fin n,
        (∑ j : Fin n, ∫ ζ, c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ) =
        ∫ ζ, ∑ j : Fin n, c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ := by
      intro i
      symm
      apply MeasureTheory.integral_finset_sum
      intro j _
      exact hIntKc i j
    have hStep3 : (∑ i : Fin n, ∑ j : Fin n,
        ∫ ζ, c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ) =
        (∑ i : Fin n, ∫ ζ, ∑ j : Fin n,
          c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ) := by
      congr 1
      ext i
      exact hStep3a i
    rw [hStep3]
    -- Then swap outer sum with integral: ∑_i ∫ = ∫ ∑_i
    have hIntInner : ∀ i : Fin n, MeasureTheory.Integrable
        (fun ζ => ∑ j : Fin n, c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j)) μ := by
      intro i
      apply MeasureTheory.integrable_finset_sum
      intro j _
      exact hIntKc i j
    symm
    calc ∫ ζ, qH ζ ∂μ
        = ∫ ζ, ∑ i : Fin n, ∑ j : Fin n,
            c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ := rfl
      _ = ∑ i : Fin n, ∫ ζ, ∑ j : Fin n,
            c i * starRingEnd ℂ (c j) * caratheodoryKernel (herglotzKernel ζ) (x i) (x j) ∂μ := by
          rw [MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hIntInner i)]

  -- Step 6: Take real parts
  have hIntqH : MeasureTheory.Integrable qH μ := by
    -- qH = ∑∑ c_i · conj(c_j) · K_{H_ζ}(x_i, x_j), a finite sum of integrable functions
    apply MeasureTheory.integrable_finset_sum
    intro i _
    apply MeasureTheory.integrable_finset_sum
    intro j _
    exact (hIntK i j).const_mul _

  have hQuadEqRe : (∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * caratheodoryKernel F (x i) (x j)).re =
      ∫ ζ, (qH ζ).re ∂μ := by
    rw [hQuadEq, ← RCLike.re_eq_complex_re]
    exact (integral_re hIntqH).symm

  -- Conclusion
  rw [hQuadEqRe]
  exact MeasureTheory.integral_nonneg_of_ae hqH_nonneg

end Caratheodory

/-!
## Connection to HilbertRealization.lean
-/

/-- The original Carathéodory definition (just non-negative real part). -/
def IsCaratheodory (Func : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, norm z < 1 → 0 ≤ (Func z).re

/-- The Carathéodory kernel (matching original definition). -/
def caratheodoryKernel' (Func : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (Func z + starRingEnd ℂ (Func w)) / (1 - z * starRingEnd ℂ w)

/--
For holomorphic functions with positive real part, kernel positivity holds.
This is the interface to HilbertRealization.lean.
-/
theorem caratheodory_positive_definite_with_holomorphy
    (Func : ℂ → ℂ)
    (hHol : Caratheodory.IsHolomorphicOnDisk Func)
    (hC : IsCaratheodory Func)
    (hHerg : Caratheodory.herglotz_representation Func
      { holomorphic := hHol
        re_nonneg := hC }) :
    ∀ (n : ℕ) (z : Fin n → ℂ) (_hz : ∀ i, norm (z i) < 1) (c : Fin n → ℂ),
      0 ≤ (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * caratheodoryKernel' Func (z i) (z j)).re := by
  intro n z hz c
  have hF : Caratheodory.IsCaratheodoryClass Func :=
    { holomorphic := hHol
      re_nonneg := hC }
  have hpos := Caratheodory.caratheodory_positive_definite Func hF hHerg n z hz c
  simp only [caratheodoryKernel', Caratheodory.caratheodoryKernel] at hpos ⊢
  exact hpos

end ExplicitFormula
end RiemannRecognitionGeometry
