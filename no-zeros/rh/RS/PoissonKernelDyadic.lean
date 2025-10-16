import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import rh.RS.PoissonKernelAnalysis

/-!
# Poisson Kernel Dyadic Geometry

This file isolates the completed dyadic separation lemmas and Schur-type bounds
required for the Poisson kernel analysis. They are split from
`PoissonKernelAnalysis` so that the latter can focus on whole-line integral
identities.
-/

noncomputable section
open Classical MeasureTheory
open scoped Interval BigOperators

namespace RH
namespace RS
namespace PoissonKernelDyadic

open PoissonKernelAnalysis

lemma Ksigma_le_inv_sigma {σ x : ℝ} (hσ : 0 < σ) : Ksigma σ x ≤ 1 / σ := by
  exact PoissonKernelAnalysis.Ksigma_le_inv_sigma (σ := σ) (x := x) hσ

lemma Ksigma_le_sigma_div_sq {σ x : ℝ} (hx : x ≠ 0) : Ksigma σ x ≤ σ / x ^ 2 := by
  exact PoissonKernelAnalysis.Ksigma_le_sigma_div_sq (σ := σ) (x := x) hx

lemma Ksigma_add_bound_of_dyadic_sep
  {σ τ sep L : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hsep : 0 < sep) (hL : 0 < L)
  {a b : ℝ} {d : ℕ}
  (hsepAB : sep * (2 : ℝ) ^ d * L ≤ |a - b|) :
  Ksigma (σ + τ) (a - b)
    ≤ ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((1 / 4 : ℝ) ^ d) := by
  have hxpos : 0 < |a - b| :=
    lt_of_le_of_lt hsepAB (by
    have : 0 < sep * (2 : ℝ) ^ d * L :=
        mul_pos (mul_pos hsep (pow_pos (by norm_num : (0 : ℝ) < 2) d)) hL
    exact this)
  have hxne : (a - b) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxpos)
  have hbound :=
    Ksigma_le_sigma_div_sq (σ := σ + τ) (x := a - b) hxne
  have hx2 : (a - b) ^ 2 ≥ (sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2) := by
    have hsq : (sep * (2 : ℝ) ^ d * L) ^ 2 ≤ |a - b| ^ 2 :=
      sq_le_sq.mpr hsepAB
    simpa [mul_pow, pow_mul, pow_two, abs_sub_comm, two_mul] using hsq
  have hx2_inv_le : 1 / (a - b) ^ 2 ≤
      (1 / (sep ^ 2 * L ^ 2)) * ((1 / 4 : ℝ) ^ d) := by
    have hx2_pos : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero _ hxne
    have hden2pos : 0 < (sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2) := by
      have h2pow : 0 < (2 : ℝ) ^ (2 * d) :=
        pow_pos (by norm_num : (0 : ℝ) < 2) _
      exact mul_pos (mul_pos (sq_pos_of_ne_zero sep (ne_of_gt hsep)) h2pow)
        (sq_pos_of_ne_zero L (ne_of_gt hL))
    have := inv_le_inv_of_le (by exact le_of_lt hden2pos) hx2
    have htwopow : (2 : ℝ) ^ (2 * d) = (4 : ℝ) ^ d := by
      simpa [pow_mul] using pow_mul (2 : ℝ) 2 d
    have : 1 / (a - b) ^ 2 ≤ 1 /
        ((sep ^ 2) * (4 : ℝ) ^ d * (L ^ 2)) :=
      by simpa [htwopow, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
  have hσt_pos : 0 < σ + τ := add_pos hσ hτ
  have : Ksigma (σ + τ) (a - b) ≤ (σ + τ) * (1 / (a - b) ^ 2) := by
    simpa [one_div, mul_comm] using hbound
  exact le_trans this <| by
    have := mul_le_mul_of_nonneg_left hx2_inv_le hσt_pos.le
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma conv_upper_bound_4decay_of_sep
    {σ τ sep L : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hsep : 0 < sep) (hL : 0 < L)
  {a b : ℝ} {d : ℕ}
  (hconv : (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
    = Real.pi * Ksigma (σ + τ) (a - b))
    (hsepAB : sep * (2 : ℝ) ^ d * L ≤ |a - b|) :
    (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
    ≤ Real.pi * ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((1 / 4 : ℝ) ^ d) := by
  have hKs := Ksigma_add_bound_of_dyadic_sep (σ := σ) (τ := τ)
    (sep := sep) (L := L) hσ hτ hsep hL (a := a) (b := b) (d := d) hsepAB
  simpa [hconv, mul_assoc, mul_left_comm, mul_comm]
    using mul_le_mul_of_nonneg_left hKs Real.pi_pos.le

def inDyadicAnnulus (c L : ℝ) (k : ℕ) (x : ℝ) : Prop :=
  (2 : ℝ) ^ k * L < |x - c| ∧ |x - c| ≤ (2 : ℝ) ^ (k + 1) * L

lemma sep_from_base_of_annulus
    {c L t x : ℝ} {k : ℕ}
    (hbase : |t - c| ≤ L) (hAnn : inDyadicAnnulus c L k x)
    (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) * L ≤ |t - x| := by
  have htri : |t - x| ≥ | |x - c| - |t - c| | := by
    simpa [abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using abs_sub_abs_le_abs_sub (x := t) (y := c) (z := x)
  have hx_rad : (2 : ℝ) ^ k * L < |x - c| := hAnn.1
  have hstep : |t - x| > (2 : ℝ) ^ k * L - L :=
    lt_of_le_of_lt
      (by
        have := sub_le_sub_right (le_of_lt hx_rad) L
        simpa using this)
      (by linarith)
  have hgeom : (2 : ℝ) ^ k * L - L ≥ (2 : ℝ) ^ (k - 1) * L := by
    have hposL : 0 ≤ L := (abs_nonneg (t - c)).trans <| (abs_le.mp hbase).2
    have hk' : (2 : ℝ) ^ k - 1 ≥ (2 : ℝ) ^ (k - 1) := by
      have hkpow : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
        have : k = (k - 1) + 1 := by
          have := Nat.succ_pred_eq_of_pos hk
          simpa [Nat.add_comm] using this.symm
        simpa [this, pow_add, pow_one, two_mul, one_mul]
          using pow_add (2 : ℝ) (k - 1) 1
      have hnonneg : 0 ≤ (2 : ℝ) ^ (k - 1) := pow_nonneg (by norm_num) _
      have : 2 * (2 : ℝ) ^ (k - 1) - 1 ≥ (2 : ℝ) ^ (k - 1) := by
        have : (2 : ℝ) ^ (k - 1) - 1 ≥ 0 := by
          have := one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (k - 1)
          linarith
        linarith
      simpa [hkpow] using this
    have := mul_le_mul_of_nonneg_right hk' hposL
    simpa [mul_sub] using this
  have : |t - x| ≥ (2 : ℝ) ^ (k - 1) * L :=
    le_of_lt <| lt_of_le_of_lt hgeom hstep
  exact this

lemma sep_between_annuli_gap_ge_two
    {c L x y : ℝ} {k j : ℕ}
    (hAnnX : inDyadicAnnulus c L k x)
    (hAnnY : inDyadicAnnulus c L j y)
    (hL : 0 < L) (hgap : 2 ≤ Nat.dist k j) :
    (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |x - y| := by
  have hkj := le_total k j
  rcases hkj with hkj | hjk
  · have hΔ : 2 ≤ k - j := by
      have : Nat.dist k j = k - j := Nat.dist_eq_sub_of_le hkj
      simpa [this] using hgap
    have htri : |x - y| ≥ | |x - c| - |y - c| | := by
      simpa [abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using abs_sub_abs_le_abs_sub (x := x) (y := c) (z := y)
    have hx_lb : (2 : ℝ) ^ k * L < |x - c| := hAnnX.1
    have hy_ub : |y - c| ≤ (2 : ℝ) ^ (j + 1) * L := hAnnY.2
    have hdiff : |x - y| ≥ (2 : ℝ) ^ k * L - (2 : ℝ) ^ (j + 1) * L := by
      have := sub_le_sub (le_of_lt hx_lb) hy_ub
      exact le_trans (by
        have := abs_abs_sub_le_abs_sub_abs (x := x - c) (y := y - c)
        simpa [abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using this) this
    have hnum : (2 : ℝ) ^ k * L - (2 : ℝ) ^ (j + 1) * L
        = (2 : ℝ) ^ j * ((2 : ℝ) ^ (k - j) - 2) * L := by
      have hk' : k = j + (k - j) := Nat.add_sub_of_le hkj
      have : (2 : ℝ) ^ k = (2 : ℝ) ^ j * (2 : ℝ) ^ (k - j) := by
        simpa [pow_add, hk'] using pow_add (2 : ℝ) j (k - j)
      have hxpow : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := by
        simpa [pow_add, pow_one] using pow_add (2 : ℝ) j 1
      simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc, this, hxpow]
        using congrArg (fun z : ℝ => z * L) (by ring)
    have hx : |x - y| ≥ (2 : ℝ) ^ j * ((2 : ℝ) ^ (k - j) - 2) * L := by
      simpa [hnum] using hdiff
    have hgeom : ((2 : ℝ) ^ (k - j) - 2) ≥ (2 : ℝ) ^ (k - j - 1) := by
      have hm : 2 ≤ k - j := hΔ
      have hkpos : 1 ≤ k - j := hm.trans (Nat.one_le_bit0 _)
      have hkdecomp : k - j = (k - j - 1) + 1 := by
        have := Nat.succ_pred_eq_of_pos hkpos
        simpa [Nat.add_comm] using this.symm
      have : (2 : ℝ) ^ (k - j) = 2 * (2 : ℝ) ^ (k - j - 1) := by
        simpa [hkdecomp, pow_add, pow_one, two_mul, one_mul]
          using pow_add (2 : ℝ) (k - j - 1) 1
      have hnonneg : 0 ≤ (2 : ℝ) ^ (k - j - 1) := pow_nonneg (by norm_num) _
      have : 2 * (2 : ℝ) ^ (k - j - 1) - 2 ≥ (2 : ℝ) ^ (k - j - 1) := by linarith
      have : (2 : ℝ) ^ (k - j) ≥ 2 + (2 : ℝ) ^ (k - j - 1) := by
        have hxpow : 2 * (2 : ℝ) ^ (k - j - 1) ≥ 2 + (2 : ℝ) ^ (k - j - 1) := by
          have hxnonneg : 0 ≤ (2 : ℝ) ^ (k - j - 1) := pow_nonneg (by norm_num) _
          linarith
        simpa [this, hkdecomp, pow_add, pow_one, two_mul, one_mul]
          using hxpow
      exact sub_le_iff_le_add'.mpr this
    have hx' : (2 : ℝ) ^ j * ((2 : ℝ) ^ (k - j) - 2) ≥ (2 : ℝ) ^ (k - j - 1) := by
      have hnonneg : 0 ≤ (2 : ℝ) ^ j := pow_nonneg (by norm_num) _
      have := one_le_pow_of_one_le (by normnum : (1 : ℝ) ≤ 2) j
      have := mul_le_mul_of_nonneg_left hgeom this
      simpa using this
    have : |x - y| ≥ (2 : ℝ) ^ (k - j - 1) * L :=
      le_trans hx (by exact mul_le_mul_of_nonneg_right hx' (le_of_lt hL))
    simpa [one_div, inv_eq_one_div, mul_comm, mul_left_comm, mul_assoc,
      pow_succ, two_mul] using this
  · have := sep_between_annuli_gap_ge_two (c := c) (L := L)
      (x := y) (y := x) (k := j) (j := k) hAnnY hAnnX hL
      (by simpa [Nat.dist_comm] using hgap)
    simpa [abs_sub_comm, Nat.dist_comm] using this

lemma row_bound_4decay
    {σ τ α L c : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hL : 0 < L)
    (S : Set ℝ) (hS : MeasurableSet S)
    (a b : ℕ → ℝ)
    (ha : ∀ k, inDyadicAnnulus c L k (a k))
    (hb : ∀ j, inDyadicAnnulus c L j (b j))
    (hconv : ∀ k j,
      (∫ t, Ksigma σ (t - a k) * Ksigma τ (t - b j))
        = Real.pi * Ksigma (σ + τ) (a k - b j))
    (nu : ℕ → ℝ) (hnu_nonneg : ∀ j, 0 ≤ nu j) :
    ∀ K k, k ∈ Finset.range K →
      (Finset.range K).sum (fun j =>
        (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          * (((1 / 4 : ℝ) ^ j) * (nu j)))
      ≤ (max (Real.pi * ((σ + τ) / ((1 / 2 : ℝ) ^ 2 * L ^ 2))) (4 * (Real.pi / (σ + τ))))
        * ((Finset.range K).sum (fun j => ((1 / 4 : ℝ) ^ j) * (nu j))) := by
  classical
  intro K k hk
  set C_far : ℝ := Real.pi * ((σ + τ) / ((1 / 2 : ℝ) ^ 2 * L ^ 2))
  set C_near : ℝ := 4 * (Real.pi / (σ + τ))
  set C_row : ℝ := max C_far C_near
  have hterm : ∀ j ∈ Finset.range K,
      (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          * (((1 / 4 : ℝ) ^ j) * (nu j))
      ≤ (C_row * ((1 / 4 : ℝ) ^ (Nat.dist k j))) * (((1 / 4 : ℝ) ^ j) * (nu j)) := by
    intro j hj
    have hnonneg_integrand : ∀ t, 0 ≤ Ksigma σ (t - a k) * Ksigma τ (t - b j) := by
      intro t; exact Ksigma_mul_nonneg (σ := σ) (τ := τ) hσ.le hτ.le t (a k) (b j)
    have hrest := integral_restrict_mono_of_nonneg
      (f := fun t => Ksigma σ (t - a k) * Ksigma τ (t - b j))
      hnonneg_integrand S hS
    have hidentity := hconv k j
    by_cases hcase : 2 ≤ Nat.dist k j
    · have hsep : (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |a k - b j| :=
        sep_between_annuli_gap_ge_two (c := c) (L := L) (x := a k) (y := b j)
          (hAnnX := ha k) (hAnnY := hb j) hL hcase
      have := conv_upper_bound_4decay_of_sep (σ := σ) (τ := τ)
        (sep := (1 / 2 : ℝ)) (L := L) hσ hτ (by norm_num) hL
        (a := a k) (b := b j) (d := Nat.dist k j) (hconv := hidentity)
        (hsepAB := hsep)
      have hx : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_far * ((1 / 4 : ℝ) ^ (Nat.dist k j)) :=
        le_trans hrest this
      have hφ_nonneg : 0 ≤ ((1 / 4 : ℝ) ^ j) * (nu j) :=
        mul_nonneg (pow_nonneg (by norm_num) _) (hnu_nonneg j)
      have hCrow_ge : C_far ≤ C_row := le_max_left _ _
      have : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_row * ((1 / 4 : ℝ) ^ (Nat.dist k j)) :=
        le_trans hx <|
          by
            have := mul_le_mul_of_nonneg_right hCrow_ge
              (pow_nonneg (by norm_num) _)
            simpa [C_far, C_row, mul_comm, mul_left_comm, mul_assoc] using this
      exact mul_le_mul_of_nonneg_right this hφ_nonneg
    · have hle : Nat.dist k j ≤ 1 := Nat.lt_succ_iff.mp (lt_of_not_ge hcase)
      have hWhole :
          (∫ t, Ksigma σ (t - a k) * Ksigma τ (t - b j))
            ≤ Real.pi / (σ + τ) := by
        have : Ksigma (σ + τ) (a k - b j) ≤ 1 / (σ + τ) :=
          Ksigma_le_inv_sigma (σ := σ + τ) (x := a k - b j) (add_pos hσ hτ)
        simpa [hidentity, mul_comm, mul_left_comm, mul_assoc]
          using mul_le_mul_of_nonneg_left this Real.pi_pos.le
      have hRestr_le := le_trans hrest hWhole
      have hCrow_ge : Real.pi / (σ + τ)
          ≤ C_row * ((1 / 4 : ℝ) ^ (Nat.dist k j)) := by
        have hdec_ge : ((1 / 4 : ℝ) ^ (Nat.dist k j)) ≥ (1 / 4 : ℝ) := by
          interval_cases Nat.dist k j using hle <;> simp
        have hmono : (1 / 4 : ℝ) ≤ ((1 / 4 : ℝ) ^ (Nat.dist k j)) :=
          (by
            interval_cases Nat.dist k j using hle <;> simp [pow_succ] at *)
        have hCpos : 0 ≤ 4 * (Real.pi / (σ + τ)) := by
          have : 0 ≤ Real.pi / (σ + τ) :=
            div_nonneg Real.pi_pos.le (add_nonneg hσ.le hτ.le)
          exact mul_nonneg (by norm_num) this
        have : (Real.pi / (σ + τ)) ≤ C_near * ((1 / 4 : ℝ) ^ (Nat.dist k j)) := by
          refine le_trans ?_ (mul_le_mul_of_nonneg_left hmono hCpos)
          have : (1 : ℝ) ≤ 4 * (1 / 4 : ℝ) := by norm_num
          have hπpos : 0 ≤ Real.pi / (σ + τ) :=
            div_nonneg Real.pi_pos.le (add_nonneg hσ.le hτ.le)
          simpa [C_near, mul_comm, mul_left_comm, mul_assoc]
            using mul_le_mul_of_nonneg_left this hπpos
        exact le_trans (le_max_right _ _) this
      have hφ_nonneg : 0 ≤ ((1 / 4 : ℝ) ^ j) * (nu j) :=
        mul_nonneg (pow_nonneg (by norm_num) _) (hnu_nonneg j)
      have : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_row * ((1 / 4 : ℝ) ^ (Nat.dist k j)) :=
        le_trans hRestr_le hCrow_ge
      exact mul_le_mul_of_nonneg_right this hφ_nonneg
  have hsum := Finset.sum_le_sum hterm
  have hdec_le_one : ∀ j ∈ Finset.range K,
      ((1 / 4 : ℝ) ^ (Nat.dist k j)) ≤ 1 := by
    intro j hj; exact pow_le_one _ (by norm_num) (by norm_num)
  have hφ_nonneg : ∀ j ∈ Finset.range K,
      0 ≤ ((1 / 4 : ℝ) ^ j) * (nu j) := by
    intro j hj; exact mul_nonneg (pow_nonneg (by norm_num) _) (hnu_nonneg j)
  have hterm2 : ∀ j ∈ Finset.range K,
      (C_row * ((1 / 4 : ℝ) ^ (Nat.dist k j))) * (((1 / 4 : ℝ) ^ j) * (nu j))
      ≤ C_row * (((1 / 4 : ℝ) ^ j) * (nu j)) := by
    intro j hj
    have := hdec_le_one j hj
    have hCpos : 0 ≤ C_row :=
      by
        have h1 : 0 ≤ C_far := by
          have hdenpos : 0 < ((1 / 2 : ℝ) ^ 2 * L ^ 2) :=
            mul_pos (by norm_num) (pow_two_pos_of_ne_zero _ (ne_of_gt hL))
          exact mul_nonneg Real.pi_pos.le
            (div_nonneg (add_nonneg hσ.le hτ.le) (le_of_lt hdenpos))
        have h2 : 0 ≤ C_near :=
          mul_nonneg (by norm_num)
            (div_nonneg Real.pi_pos.le (add_nonneg hσ.le hτ.le))
        exact max_nonneg h1 h2
    have := mul_le_mul_of_nonneg_left this hCpos
    have := mul_le_mul_of_nonneg_right this (hφ_nonneg j hj)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hsum2 := Finset.sum_le_sum hterm2
  have hfac : (Finset.range K).sum
      (fun j => C_row * (((1 / 4 : ℝ) ^ j) * (nu j)))
      = C_row * ((Finset.range K).sum (fun j => ((1 / 4 : ℝ) ^ j) * (nu j))) := by
    simpa using Finset.mul_sum C_row (Finset.range K)
      (fun j => ((1 / 4 : ℝ) ^ j) * (nu j))
  exact le_trans hsum <|
    by simpa [hfac, C_row, mul_comm, mul_left_comm, mul_assoc] using hsum2

lemma Ksigma_le_inv_sigma' {σ x : ℝ} (hσ : 0 < σ) : PoissonKernelAnalysis.Ksigma σ x ≤ 1 / σ :=
  PoissonKernelAnalysis.Ksigma_le_inv_sigma (σ := σ) (x := x) hσ

lemma Ksigma_mul_nonneg
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (t a b : ℝ) :
    0 ≤ Ksigma σ (t - a) * Ksigma τ (t - b) := by
  simpa using
    PoissonKernelAnalysis.Ksigma_mul_nonneg (σ := σ) (τ := τ)
      (t := t) (a := a) (b := b) hσ hτ

lemma Ksigma_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Ksigma σ x :=
  PoissonKernelAnalysis.Ksigma_nonneg (σ := σ) (x := x) hσ

-- /-- Monotonicity of integral under restriction to a measurable set for nonnegative functions. -/
-- lemma integral_restrict_mono_of_nonneg
--     {f : ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
--     (S : Set ℝ) (hS : MeasurableSet S) :
--     (∫ x in S, f x) ≤ (∫ x, f x) := by
--   have hAE : (fun x => f x) =ᵐ[Measure.restrict volume S] (fun x => f x) := by
--     simp
--   have h_nonneg : 0 ≤ᵐ[Measure.restrict volume S] (fun x => f x) :=
--     Filter.Eventually.of_forall (by intro x; exact hf_nonneg x)
--   simpa using integral_mono_measure (μ := Measure.restrict volume S) (ν := volume)
--     (f := fun x => f x) (g := fun x => f x)
--     (by intro x; simp) (by intro x; simp)
--     (by simp [hS]) (by simp) (le_of_eq (by simp [hAE])) h_nonneg

lemma sep_lower_bound (t a b : ℝ) : |t - b| ≥ |a - b| - |t - a| := by
  have : |a - b| ≤ |a - t| + |t - b| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_sub_comm]
      using abs_add (a - t) (t - b)
  simpa [sub_eq_add_neg, abs_sub_comm] using sub_le_iff_le_add'.mpr this

end PoissonKernelDyadic
end RS
end RH
