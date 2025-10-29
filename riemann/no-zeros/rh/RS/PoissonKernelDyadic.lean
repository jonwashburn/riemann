import rh.Compat
import rh.RS.PoissonKernelAnalysis

/-!
# Poisson Kernel Dyadic Geometry

This file isolates dyadic separation lemmas and Schur-type bounds for the
Poisson kernel analysis. It is intentionally lightweight and self-contained.
-/

noncomputable section
open Classical MeasureTheory
open scoped Interval BigOperators

namespace RH
namespace RS
namespace PoissonKernelDyadic

/-- Poisson/Cauchy kernel `K_σ(x) = σ / (x^2 + σ^2)`. -/
@[simp] def Ksigma (σ x : ℝ) : ℝ := σ / (x^2 + σ^2)

lemma Ksigma_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Ksigma σ x := by
  unfold Ksigma
  have hden : 0 ≤ x^2 + σ^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact div_nonneg hσ hden

lemma Ksigma_mul_nonneg {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (t a b : ℝ) :
    0 ≤ Ksigma σ (t - a) * Ksigma τ (t - b) := by
  exact mul_nonneg (Ksigma_nonneg (σ := σ) (x := t - a) hσ)
                   (Ksigma_nonneg (σ := τ) (x := t - b) hτ)

lemma Ksigma_le_inv_sigma {σ x : ℝ} (hσ : 0 < σ) : Ksigma σ x ≤ 1 / σ := by
  unfold Ksigma
  have hden : σ ^ 2 ≤ x ^ 2 + σ ^ 2 := by
    have hx : 0 ≤ x ^ 2 := sq_nonneg _
    linarith
  have hσ2pos : 0 < σ ^ 2 := pow_pos hσ 2
  have hone := one_div_le_one_div_of_le hσ2pos hden
  have hmul := mul_le_mul_of_nonneg_left hone hσ.le
  have hEq : σ / σ ^ 2 = 1 / σ := by
    have hne : σ ≠ 0 := ne_of_gt hσ
    calc
      σ / σ ^ 2 = σ / (σ * σ) := by simp [pow_two]
      _ = (σ / σ) / σ := by simpa using (div_mul_eq_div_div σ σ σ)
      _ = 1 / σ := by simp [hne]
  have : σ / (x ^ 2 + σ ^ 2) ≤ σ / σ ^ 2 := by
    simpa [div_eq_mul_inv] using hmul
  exact this.trans (by simpa [hEq])

lemma Ksigma_le_sigma_div_sq {σ x : ℝ} (hσ : 0 ≤ σ) (hx : x ≠ 0) :
    Ksigma σ x ≤ σ / x^2 := by
  unfold Ksigma
  have hden : x ^ 2 ≤ x ^ 2 + σ ^ 2 := by
    have hσ' : 0 ≤ σ ^ 2 := by simpa using sq_nonneg σ
    linarith
  have hxpos : 0 < x ^ 2 := by simpa using (sq_pos_of_ne_zero x hx)
  have hone := one_div_le_one_div_of_le hxpos hden
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hone hσ


/-! ### Dyadic separation bound for `Ksigma` -/

lemma Ksigma_add_bound_of_dyadic_sep
  {σ τ sep L : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hsep : 0 < sep) (hL : 0 < L)
  {a b : ℝ} {d : ℕ}
  (hsepAB : sep * (2 : ℝ) ^ d * L ≤ |a - b|) :
  Ksigma (σ + τ) (a - b)
    ≤ ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
  -- crude decay: σ+τ over square
  have hne : a - b ≠ 0 := by
    have hpos : 0 < sep * (2 : ℝ) ^ d * L := mul_pos (mul_pos hsep (pow_pos (by norm_num) d)) hL
    have : 0 < |a - b| := lt_of_lt_of_le hpos hsepAB
    exact abs_pos.mp this
  have hbound := Ksigma_le_sigma_div_sq (σ := σ + τ) (x := a - b) (add_pos hσ hτ).le hne
  -- square lower bound
  have hsq : (a - b) ^ 2 ≥ sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2 := by
    have hx : 0 ≤ sep * (2 : ℝ) ^ d * L := by positivity
    have hAbs : |sep * (2 : ℝ) ^ d * L| ≤ |a - b| := by simpa [abs_of_nonneg hx] using hsepAB
    have hsq' : (sep * (2 : ℝ) ^ d * L) ^ 2 ≤ (a - b) ^ 2 := by
      simpa using (sq_le_sq.mpr hAbs)
    have hsq'' : sep ^ 2 * ((2 : ℝ) ^ d) ^ 2 * L ^ 2 ≤ (a - b) ^ 2 := by
      simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hsq'
    have hsq''' : sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2 ≤ (a - b) ^ 2 := by
      simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using hsq''
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq'''
  -- invert the square inequality
  have hpos_den : 0 < sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2 := by
    have : 0 < (2 : ℝ) ^ (d * 2) := pow_pos (by norm_num) _
    exact mul_pos (mul_pos (pow_pos hsep 2) this) (pow_pos hL 2)
  have hinv : 1 / (a - b) ^ 2 ≤ (1 / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by

    have hmono : 1 / (a - b) ^ 2 ≤ 1 / (sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2) :=
      one_div_le_one_div_of_le hpos_den hsq
    have hrot :
        1 / (sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2)
        = 1 / ((sep ^ 2 * L ^ 2) * (2 : ℝ) ^ (d * 2)) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    have hsplit :
        1 / ((sep ^ 2 * L ^ 2) * (2 : ℝ) ^ (d * 2))
        = (1 / (sep ^ 2 * L ^ 2)) * ((2 : ℝ) ^ (d * 2))⁻¹ := by
      simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
        (one_div_mul_one_div (sep ^ 2 * L ^ 2) ((2 : ℝ) ^ (d * 2))).symm
    have hpow : ((2 : ℝ) ^ (d * 2)) = (4 : ℝ) ^ d := by
      simpa [Nat.mul_comm] using (RH.two_pow_two_mul_eq_four_pow d)
    have : 1 / (sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2)
        = (1 / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
      -- rotate, then split, then rewrite powers
      calc
        1 / (sep ^ 2 * (2 : ℝ) ^ (d * 2) * L ^ 2)
            = 1 / ((sep ^ 2 * L ^ 2) * (2 : ℝ) ^ (d * 2)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (1 / (sep ^ 2 * L ^ 2)) * ((2 : ℝ) ^ (d * 2))⁻¹ := by
              simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
                (one_div_mul_one_div (sep ^ 2 * L ^ 2) ((2 : ℝ) ^ (d * 2))).symm
        _ = (1 / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by simpa [hpow]
    exact hmono.trans (by simpa [this])
  -- combine
  have hσt_pos : 0 ≤ σ + τ := add_nonneg hσ.le hτ.le
  have hbound' : Ksigma (σ + τ) (a - b) ≤ (σ + τ) * (1 / (a - b) ^ 2) := by
    simpa [div_eq_mul_inv, one_div, mul_comm] using hbound
  have hb2 : (σ + τ) * (1 / (a - b) ^ 2)
      ≤ ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hinv hσt_pos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  exact hbound'.trans hb2

lemma conv_upper_bound_4decay_of_sep
    {σ τ sep L : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hsep : 0 < sep) (hL : 0 < L)
    {a b : ℝ} {d : ℕ}
    (hconv : (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
      = Real.pi * Ksigma (σ + τ) (a - b))
    (hsepAB : sep * (2 : ℝ) ^ d * L ≤ |a - b|) :
    (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
      ≤ Real.pi * ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
  have hKs := Ksigma_add_bound_of_dyadic_sep (σ := σ) (τ := τ)
    (sep := sep) (L := L) hσ hτ hsep hL (a := a) (b := b) (d := d) hsepAB
  have hπKs := mul_le_mul_of_nonneg_left hKs Real.pi_pos.le
  calc
    (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
        = Real.pi * Ksigma (σ + τ) (a - b) := by simpa [hconv]
    _ ≤ Real.pi * ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hπKs

/-! ### Integrability of product kernel -/

lemma Ksigma_prod_integrable {σ τ a b : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    Integrable (fun t => Ksigma σ (t - a) * Ksigma τ (t - b)) := by
  -- define the integrand and the majorant
  let f : ℝ → ℝ := fun t => Ksigma σ (t - a) * Ksigma τ (t - b)
  let cσ : ℝ := min (1 : ℝ) (σ ^ 2)
  let cτ : ℝ := min (1 : ℝ) (τ ^ 2)
  have cσ_pos : 0 < cσ := lt_min_iff.mpr ⟨by norm_num, pow_pos hσ 2⟩
  have cτ_pos : 0 < cτ := lt_min_iff.mpr ⟨by norm_num, pow_pos hτ 2⟩
  have cσ_le_one : cσ ≤ 1 := min_le_left _ _
  have cτ_le_one : cτ ≤ 1 := min_le_left _ _
  have cσ_le_sq : cσ ≤ σ ^ 2 := min_le_right _ _
  have cτ_le_sq : cτ ≤ τ ^ 2 := min_le_right _ _
  have invA : ∀ t, ((t - a) ^ 2 + σ ^ 2)⁻¹ ≤ (cσ * (1 + (t - a) ^ 2))⁻¹ := by
    intro t
    have hsum : cσ + cσ * (t - a) ^ 2 ≤ σ ^ 2 + (t - a) ^ 2 := by
      have hmul : cσ * (t - a) ^ 2 ≤ 1 * (t - a) ^ 2 :=
        mul_le_mul_of_nonneg_right cσ_le_one (sq_nonneg _)
      simpa [one_mul] using add_le_add cσ_le_sq hmul
    have hpos : 0 < cσ * (1 + (t - a) ^ 2) := mul_pos cσ_pos (by linarith [sq_nonneg (t - a)])
    have hrewrite : cσ * (1 + (t - a) ^ 2) = cσ + cσ * (t - a) ^ 2 := by ring
    have hrewrite' : (t - a) ^ 2 + σ ^ 2 = σ ^ 2 + (t - a) ^ 2 := by ac_rfl
    have hle : cσ * (1 + (t - a) ^ 2) ≤ (t - a) ^ 2 + σ ^ 2 := by
      simpa [hrewrite, hrewrite'] using hsum
    exact RH.inv_le_inv_of_le hpos hle
  have invB : ∀ t, ((t - b) ^ 2 + τ ^ 2)⁻¹ ≤ (cτ * (1 + (t - b) ^ 2))⁻¹ := by
    intro t
    have hsum : cτ + cτ * (t - b) ^ 2 ≤ τ ^ 2 + (t - b) ^ 2 := by
      have hmul : cτ * (t - b) ^ 2 ≤ 1 * (t - b) ^ 2 :=
        mul_le_mul_of_nonneg_right cτ_le_one (sq_nonneg _)
      simpa [one_mul] using add_le_add cτ_le_sq hmul
    have hpos : 0 < cτ * (1 + (t - b) ^ 2) := mul_pos cτ_pos (by linarith [sq_nonneg (t - b)])
    have hrewrite : cτ * (1 + (t - b) ^ 2) = cτ + cτ * (t - b) ^ 2 := by ring
    have hrewrite' : (t - b) ^ 2 + τ ^ 2 = τ ^ 2 + (t - b) ^ 2 := by ac_rfl
    have hle : cτ * (1 + (t - b) ^ 2) ≤ (t - b) ^ 2 + τ ^ 2 := by
      simpa [hrewrite, hrewrite'] using hsum
    exact RH.inv_le_inv_of_le hpos hle
  -- majorant g
  let C : ℝ := (σ * τ) * (cσ * cτ)⁻¹
  let g : ℝ → ℝ := fun t => C * (1 + (t - a) ^ 2)⁻¹
  -- nonnegativity
  have hf_nonneg : ∀ t, 0 ≤ f t := by
    intro t; exact Ksigma_mul_nonneg (σ := σ) (τ := τ) hσ.le hτ.le t a b
  have hg_nonneg : ∀ t, 0 ≤ g t := by
    intro t
    have : 0 ≤ (1 + (t - a) ^ 2)⁻¹ := by
      have : (0 : ℝ) ≤ 1 + (t - a) ^ 2 := by linarith [sq_nonneg (t - a)]
      simpa [one_div] using inv_nonneg.mpr this
    have : 0 ≤ C := by positivity
    exact mul_nonneg this ‹0 ≤ (1 + (t - a) ^ 2)⁻¹›
  -- domination f ≤ g
  have hdom : ∀ t, f t ≤ g t := by
    intro t
    -- bound each kernel by constants times inverse quadratics
    have hKA' : Ksigma σ (t - a) ≤ σ / (cσ * (1 + (t - a) ^ 2)) := by
      unfold Ksigma
      have := invA t
      have hσ_nonneg : 0 ≤ σ := hσ.le
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using (mul_le_mul_of_nonneg_left this hσ_nonneg)
    have hKB' : Ksigma τ (t - b) ≤ τ / (cτ * (1 + (t - b) ^ 2)) := by
      unfold Ksigma
      have := invB t
      have hτ_nonneg : 0 ≤ τ := hτ.le
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using (mul_le_mul_of_nonneg_left this hτ_nonneg)
    have hKA : Ksigma σ (t - a) ≤ (σ / cσ) * (1 + (t - a) ^ 2)⁻¹ := by
      simpa [div_mul_eq_mul_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hKA'
    have hKB : Ksigma τ (t - b) ≤ (τ / cτ) * (1 + (t - b) ^ 2)⁻¹ := by
      simpa [div_mul_eq_mul_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hKB'
    have hmul := mul_le_mul hKA hKB
      (by exact Ksigma_nonneg (σ := τ) (x := t - b) hτ.le)
      (by
        have : 0 ≤ (σ / cσ) := by positivity
        have : 0 ≤ (1 + (t - a) ^ 2)⁻¹ := by
          have : (0 : ℝ) ≤ 1 + (t - a) ^ 2 := by linarith [sq_nonneg (t - a)]
          simpa [one_div] using inv_nonneg.mpr this
        exact mul_nonneg ‹0 ≤ (σ / cσ)› this)
    -- drop the (1 + (t - b)^2)⁻¹ ≤ 1
    have hdrop1 : (1 + (t - b) ^ 2)⁻¹ ≤ (1 : ℝ) := by
      have : (1 : ℝ) ≤ 1 + (t - b) ^ 2 := by linarith [sq_nonneg (t - b)]
      have h1 : 0 < (1 : ℝ) := by norm_num
      simpa [one_div] using RH.inv_le_inv_of_le h1 this
    have hτc_nonneg : 0 ≤ (τ / cτ) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hdrop1 hτc_nonneg
    have hprod_drop :
        ((σ / cσ) * (1 + (t - a) ^ 2)⁻¹) * ((τ / cτ) * (1 + (t - b) ^ 2)⁻¹)
          ≤ ((σ / cσ) * (1 + (t - a) ^ 2)⁻¹) * ((τ / cτ) * 1) := by
      have hσfac_nonneg : 0 ≤ ((σ / cσ) * (1 + (t - a) ^ 2)⁻¹) := by
        have : 0 ≤ (σ / cσ) := by positivity
        have : 0 ≤ (1 + (t - a) ^ 2)⁻¹ := by
          have : (0 : ℝ) ≤ 1 + (t - a) ^ 2 := by linarith [sq_nonneg (t - a)]
          simpa [one_div] using inv_nonneg.mpr this
        exact mul_nonneg ‹0 ≤ (σ / cσ)› this
      exact mul_le_mul_of_nonneg_left hstep hσfac_nonneg
    have hmul_le : f t ≤ ((σ / cσ) * (1 + (t - a) ^ 2)⁻¹) * ((τ / cτ) * (1 + (t - b) ^ 2)⁻¹) := by
      simpa [f, Ksigma, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have : f t ≤ ((σ / cσ) * (1 + (t - a) ^ 2)⁻¹) * ((τ / cτ) * 1) :=
      le_trans hmul_le hprod_drop
    have : f t ≤ ((σ / cσ) * (1 + (t - a) ^ 2)⁻¹) * ((τ / cτ) * 1) := this
    have : f t ≤ ((σ / cσ) * (τ / cτ)) * (1 + (t - a) ^ 2)⁻¹ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : f t ≤ ((σ * τ) * (cσ * cτ)⁻¹) * (1 + (t - a) ^ 2)⁻¹ := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [g, C, mul_comm, mul_left_comm, mul_assoc] using this
  -- integrable majorant
  have hint_g : Integrable g := by
    have hbase : Integrable (fun t : ℝ => 1 / (1 + (t - a) ^ 2)) := by
      simpa [sub_eq_add_neg, pow_two] using (integrable_inv_one_add_sq.comp_sub_right a)
    have hmul : Integrable (fun t : ℝ => C * (1 / (1 + (t - a) ^ 2))) :=
      hbase.const_mul C
    simpa [g, one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
  -- conclude dominated
  have h_nonneg_ae : 0 ≤ᵐ[volume] f := Filter.Eventually.of_forall hf_nonneg
  have h_le_ae : f ≤ᵐ[volume] g := Filter.Eventually.of_forall hdom
  exact (Integrable.of_nonneg_of_le (μ := volume) (f := f) (g := g) h_nonneg_ae h_le_ae hint_g)

/-! ### Monotonicity for restriction -/

lemma integral_restrict_mono_of_nonneg
    {f : ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (S : Set ℝ) (hS : MeasurableSet S) (hf_int : Integrable f volume) :
    (∫ x in S, f x) ≤ (∫ x, f x) := by
  have h_nonneg_vol : 0 ≤ᵐ[volume] fun x => f x :=
    Filter.Eventually.of_forall hf_nonneg
  have hle : Measure.restrict volume S ≤ volume := Measure.restrict_le_self
  simpa using
    (integral_mono_measure (μ := Measure.restrict volume S) (ν := volume)
      hle h_nonneg_vol hf_int)

/-- `x` lies in the dyadic annulus `k` around center `c` with radius scale `L`. -/
def inDyadicAnnulus (c L : ℝ) (k : ℕ) (x : ℝ) : Prop :=
  (2 : ℝ) ^ k * L < |x - c| ∧ |x - c| ≤ (2 : ℝ) ^ (k + 1) * L

/-! ### Geometry: separation from base point and between annuli -/

lemma sep_from_base_of_annulus
    {c L t x : ℝ} {k : ℕ}
    (hbase : |t - c| ≤ L) (hAnn : inDyadicAnnulus c L k x)
    (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) * L ≤ |t - x| := by
  have hL_nonneg : 0 ≤ L := (abs_nonneg (t - c)).trans hbase
  -- triangle inequality: |t - x| ≥ | |x - c| - |t - c| |
  have htri : abs (|x - c| - |t - c|) ≤ abs (t - x) := by
    simpa [sub_eq_add_neg, abs_sub_comm] using
      (abs_abs_sub_abs_le_abs_sub (x - c) (t - c))
  have hx_lb : (2 : ℝ) ^ k * L ≤ |x - c| := le_of_lt hAnn.1
  have hA : (2 : ℝ) ^ k * L - L ≤ |t - x| := by
    have hx_lb' : (2 : ℝ) ^ k * L ≤ |x - c| := hx_lb
    have hstepA : (2 : ℝ) ^ k * L - L ≤ (2 : ℝ) ^ k * L - |t - c| := by
      have : -L ≤ -|t - c| := by simpa using (neg_le_neg hbase)
      simpa [sub_eq_add_neg] using add_le_add_left this _
    have hstepB : (2 : ℝ) ^ k * L - |t - c| ≤ |x - c| - |t - c| := by
      simpa [sub_eq_add_neg] using add_le_add_right hx_lb' _
    have hstepC : |x - c| - |t - c| ≤ abs (|x - c| - |t - c|) := le_abs_self _
    have hstepD : abs (|x - c| - |t - c|) ≤ abs (t - x) := by
      simpa [sub_eq_add_neg, abs_sub_comm] using
        (abs_abs_sub_abs_le_abs_sub (x - c) (t - c))
    exact le_trans hstepA (le_trans hstepB (le_trans hstepC hstepD))
  -- compare 2^(k-1)L with (2^k L - L) = (2^k - 1) L
  have hone_le_pow : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by
    simpa using (one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (k - 1))
  have hpow_le : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k - 1 := by
    -- since 2^k = 2 * 2^(k-1), we have 2^(k-1) ≤ 2*2^(k-1) - 1
    have hdecomp : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
      have : k = (k - 1) + 1 := Nat.succ_pred_eq_of_pos hk
      simpa [this, pow_add, pow_one, two_mul, one_mul] using pow_add (2 : ℝ) (k - 1) 1
    have : (2 : ℝ) ^ (k - 1) ≤ 2 * (2 : ℝ) ^ (k - 1) - 1 := by
      have : (2 : ℝ) ^ (k - 1) - 1 ≤ 2 * (2 : ℝ) ^ (k - 1) - 1 := by
        have : (2 : ℝ) ^ (k - 1) ≤ 2 * (2 : ℝ) ^ (k - 1) := by
          have hnonneg : 0 ≤ (2 : ℝ) ^ (k - 1) := by
            exact pow_nonneg (by norm_num) _
          have : (1 : ℝ) ≤ 2 := by norm_num
          simpa [one_mul] using mul_le_mul_of_nonneg_right this hnonneg
        exact sub_le_sub_right this 1
      exact le_trans (le_of_lt (lt_of_le_of_lt hone_le_pow (lt_add_one _))) this
    simpa [hdecomp] using this
  have hB : (2 : ℝ) ^ (k - 1) * L ≤ (2 : ℝ) ^ k * L - L := by
    have := mul_le_mul_of_nonneg_right hpow_le hL_nonneg
    simpa [mul_sub, one_mul] using this
  exact le_trans hB hA

lemma sep_between_annuli_gap_ge_two
    {c L x y : ℝ} {k j : ℕ}
    (hAnnX : inDyadicAnnulus c L k x)
    (hAnnY : inDyadicAnnulus c L j y)
    (hL : 0 < L) (hgap : 2 ≤ Nat.dist k j) :
    (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |x - y| := by
  have hkj := le_total k j
  rcases hkj with hkj | hjk
  · -- case k ≤ j
    have hΔ : 2 ≤ j - k := by simpa [Nat.dist_eq_sub_of_le hkj] using hgap
    -- triangle inequality and annulus bounds
    have htri : abs (|y - c| - |x - c|) ≤ abs (x - y) := by
      simpa [sub_eq_add_neg, abs_sub_comm] using
        (abs_abs_sub_abs_le_abs_sub (y - c) (x - c))
    have hy_lb : (2 : ℝ) ^ j * L ≤ |y - c| := le_of_lt hAnnY.1
    have hx_ub : |x - c| ≤ (2 : ℝ) ^ (k + 1) * L := hAnnX.2
    have hdiff : (2 : ℝ) ^ j * L - (2 : ℝ) ^ (k + 1) * L ≤ |x - y| := by
      calc
        (2 : ℝ) ^ j * L - (2 : ℝ) ^ (k + 1) * L
            ≤ (2 : ℝ) ^ j * L - |x - c| := by exact sub_le_sub_left hx_ub _
        _ ≤ abs (|y - c| - |x - c|) :=
          le_trans (sub_le_sub_right hy_lb _) (le_abs_self _)
        _ ≤ abs (x - y) := by
          simpa [sub_eq_add_neg, abs_sub_comm] using
            (abs_abs_sub_abs_le_abs_sub (y - c) (x - c))
    have hLnonneg : 0 ≤ L := le_of_lt hL
    -- show 2^(j-1)L ≤ (2^j - 2^(k+1))L
    have hk1 : k + 1 ≤ j - 1 := by
      have : k + 2 ≤ j := by
        simpa [Nat.add_sub_of_le hkj] using Nat.add_le_add_left hΔ k
      exact Nat.le_pred_of_lt (Nat.succ_lt_of_lt (Nat.succ_lt_of_lt this))
    have hpow_mono : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (j - 1) :=
      pow_le_pow_of_le_right (by norm_num : (0 : ℝ) ≤ 2) hk1
    have h2jm1 : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
      have : j = (j - 1) + 1 :=
        Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_succ_self _))
      simpa [this, pow_add, pow_one, two_mul, one_mul] using pow_add (2 : ℝ) (j - 1) 1
    have hstrong : (2 : ℝ) ^ (j - 1) * L ≤ (2 : ℝ) ^ j * L - (2 : ℝ) ^ (k + 1) * L := by
      have : (2 : ℝ) ^ (j - 1) + (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j := by
        have : (2 : ℝ) ^ (j - 1) + (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (j - 1) + (2 : ℝ) ^ (j - 1) :=
          add_le_add le_rfl hpow_mono
        simpa [h2jm1, two_mul] using this
      have := sub_le_iff_le_add'.mpr this
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_right this hLnonneg)
    have hmain : (2 : ℝ) ^ (j - 1) * L ≤ |x - y| := le_trans hstrong hdiff
    -- compare (1/2) * 2^(j-k) * L with 2^(j-1) * L
    have hmono_exp : j - k - 1 ≤ j - 1 := Nat.sub_le_sub_right (Nat.sub_le _ _) 1
    have hpow_mono' : (2 : ℝ) ^ (j - k - 1) ≤ (2 : ℝ) ^ (j - 1) :=
      pow_le_pow_of_le_right (by norm_num : (0 : ℝ) ≤ 2) hmono_exp
    have hrewrite : (1 / 2 : ℝ) * (2 : ℝ) ^ (j - k) = (2 : ℝ) ^ (j - k - 1) := by
      have hsucc : (2 : ℝ) ^ (j - k) = 2 * (2 : ℝ) ^ (j - k - 1) := by
        simpa [pow_succ] using pow_succ (2 : ℝ) (j - k - 1)
      have := congrArg (fun z => (1 / 2 : ℝ) * z) hsucc
      simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
    have hstep : (1 / 2 : ℝ) * (2 : ℝ) ^ (j - k) * L ≤ (2 : ℝ) ^ (j - 1) * L := by
      have := mul_le_mul_of_nonneg_right hpow_mono' hLnonneg
      simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using this
    have hfinal : (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |x - y| := by
      have hdist : (Nat.dist k j) = j - k := by simpa [Nat.dist_eq_sub_of_le hkj]
      simpa [hdist, mul_comm, mul_left_comm, mul_assoc] using hstep.trans hmain
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfinal
  · -- symmetric case j ≤ k
    have := sep_between_annuli_gap_ge_two (c := c) (L := L) (x := y) (y := x)
      (k := j) (j := k) hAnnY hAnnX hL (by simpa [Nat.dist_comm] using hgap)
    simpa [abs_sub_comm, Nat.dist_comm] using this

/-! ### Row bound with 4-decay -/

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
          * (((4 : ℝ) ^ j)⁻¹ * (nu j)))
      ≤ (max (Real.pi * ((σ + τ) / ((1 / 2 : ℝ) ^ 2 * L ^ 2))) (4 * (Real.pi / (σ + τ))))
        * ((Finset.range K).sum (fun j => ((4 : ℝ) ^ j)⁻¹ * (nu j))) := by
  classical
  intro K k hk
  set C_far : ℝ := Real.pi * ((σ + τ) / ((1 / 2 : ℝ) ^ 2 * L ^ 2))
  set C_near : ℝ := 4 * (Real.pi / (σ + τ))
  set C_row : ℝ := max C_far C_near
  have hterm : ∀ j ∈ Finset.range K,
      (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          * (((4 : ℝ) ^ j)⁻¹ * (nu j))
      ≤ (C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹) * (((4 : ℝ) ^ j)⁻¹ * (nu j)) := by
    intro j hj
    have hnonneg_integrand : ∀ t, 0 ≤ Ksigma σ (t - a k) * Ksigma τ (t - b j) := by
      intro t; exact Ksigma_mul_nonneg (σ := σ) (τ := τ) hσ.le hτ.le t (a k) (b j)
    have hfi : Integrable (fun t => Ksigma σ (t - a k) * Ksigma τ (t - b j)) :=
      Ksigma_prod_integrable (σ := σ) (τ := τ) (a := a k) (b := b j) hσ hτ
    have hrest := integral_restrict_mono_of_nonneg
      (f := fun t => Ksigma σ (t - a k) * Ksigma τ (t - b j)) hnonneg_integrand S hS hfi
    by_cases hcase : 2 ≤ Nat.dist k j
    · -- far-case
      have hsep : (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |a k - b j| :=
        sep_between_annuli_gap_ge_two (c := c) (L := L) (x := a k) (y := b j)
          (hAnnX := ha k) (hAnnY := hb j) hL hcase
      have hfar := conv_upper_bound_4decay_of_sep (σ := σ) (τ := τ) (sep := (1 / 2 : ℝ))
        (L := L) hσ hτ (by norm_num) hL (a := a k) (b := b j)
        (d := Nat.dist k j) (hconv := hconv k j) (hsepAB := hsep)
      have hx : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_far * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := le_trans hrest hfar
      have hφ_nonneg : 0 ≤ ((4 : ℝ) ^ j)⁻¹ * (nu j) :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) (hnu_nonneg j)
      have hx' : C_far * ((4 : ℝ) ^ (Nat.dist k j))⁻¹
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
        have : C_far ≤ C_row := le_max_left _ _
        exact mul_le_mul_of_nonneg_right this (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
      have : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := le_trans hx hx'
      exact mul_le_mul_of_nonneg_right this hφ_nonneg
    · -- near-case: dist ∈ {0,1}
      have hle : Nat.dist k j ≤ 1 := Nat.lt_succ_iff.mp (lt_of_not_ge hcase)
      have hWhole :
          (∫ t, Ksigma σ (t - a k) * Ksigma τ (t - b j))
            ≤ Real.pi / (σ + τ) := by
        calc
          (∫ t, Ksigma σ (t - a k) * Ksigma τ (t - b j))
              = Real.pi * Ksigma (σ + τ) (a k - b j) := by
                simpa [Ksigma, mul_comm, mul_left_comm, mul_assoc] using (hconv k j)
          _ ≤ Real.pi / (σ + τ) := by
            have : Ksigma (σ + τ) (a k - b j) ≤ 1 / (σ + τ) :=
              Ksigma_le_inv_sigma (σ := σ + τ) (x := a k - b j) (add_pos hσ hτ)
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_le_mul_of_nonneg_left this Real.pi_pos.le)
      have hRestr_le := le_trans hrest hWhole
      have hCrow_ge : Real.pi / (σ + τ) ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
        have hposπ : 0 ≤ Real.pi / (σ + τ) :=
          div_nonneg Real.pi_pos.le (add_nonneg hσ.le hτ.le)
        have hrow_ge_near : C_near ≤ C_row := le_max_right _ _
        have hrow_mul_ge : C_near * ((4 : ℝ) ^ (Nat.dist k j))⁻¹
            ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hrow_ge_near (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
        by_cases h0 : Nat.dist k j = 0
        · have hpow0 : ((4 : ℝ) ^ (Nat.dist k j))⁻¹ = 1 := by
            simpa [h0, pow_zero, inv_one]
          have hbase : Real.pi / (σ + τ) ≤ C_near * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
            -- since ((4)^0)⁻¹ = 1, and C_near = 4 * (Real.pi / (σ + τ)) ≥ Real.pi / (σ + τ)
            have : Real.pi / (σ + τ) ≤ 4 * (Real.pi / (σ + τ)) := by
              have := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 4) hposπ
              simpa [one_mul] using this
            simpa [C_near, hpow0, mul_comm, mul_left_comm, mul_assoc] using this
          exact hbase.trans hrow_mul_ge
        · have hd1 : Nat.dist k j = 1 := by
            have hle1 : Nat.dist k j ≤ 1 := hle
            have hge1 : 1 ≤ Nat.dist k j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
            exact le_antisymm hle1 hge1
          have hpow1 : ((4 : ℝ) ^ (Nat.dist k j))⁻¹ = (4 : ℝ)⁻¹ := by
            simpa [hd1, pow_one]
          have hbase : Real.pi / (σ + τ) ≤ C_near * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
            -- equality case: C_near * (4)⁻¹ = Real.pi / (σ + τ)
            have : C_near * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ = Real.pi / (σ + τ) := by
              simpa [C_near, hpow1, mul_comm, mul_left_comm, mul_assoc]
            exact this.ge
          exact hbase.trans hrow_mul_ge
      have hφ_nonneg : 0 ≤ ((4 : ℝ) ^ j)⁻¹ * (nu j) :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) (hnu_nonneg j)
      have : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := le_trans hRestr_le hCrow_ge
      exact mul_le_mul_of_nonneg_right this hφ_nonneg
  -- sum all j and simplify factor C_row
  let weight : ℕ → ℝ := fun j => ((4 : ℝ) ^ j)⁻¹ * (nu j)
  have hsum := Finset.sum_le_sum hterm
  have hdec_le_one : ∀ j ∈ Finset.range K, ((4 : ℝ) ^ (Nat.dist k j))⁻¹ ≤ 1 := by
    intro j hj
    have : (1 : ℝ) ≤ (4 : ℝ) ^ (Nat.dist k j) :=
      one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 4) _
    have : 1 / (4 : ℝ) ^ (Nat.dist k j) ≤ 1 / 1 := one_div_le_one_div_of_le (by norm_num) this
    simpa [one_div] using this
  have hφ_nonneg : ∀ j ∈ Finset.range K, 0 ≤ ((4 : ℝ) ^ j)⁻¹ * (nu j) := by
    intro j hj; exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) (hnu_nonneg j)
  have hterm2 : ∀ j ∈ Finset.range K,
      (C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹) * (weight j)
        ≤ C_row * (weight j) := by
    intro j hj
    have := hdec_le_one j hj
    have hCpos : 0 ≤ C_row := by
      have h1 : 0 ≤ C_far := by
        have hdenpos : 0 < ((1 / 2 : ℝ) ^ 2 * L ^ 2) := by
          have : 0 < (1 / 2 : ℝ) := by norm_num
          have h1 : 0 < (1 / 2 : ℝ) ^ 2 := pow_pos this 2
          have h2 : 0 < L ^ 2 := pow_pos hL 2
          exact mul_pos h1 h2
        exact mul_nonneg Real.pi_pos.le (div_nonneg (add_nonneg hσ.le hτ.le) (le_of_lt hdenpos))
      dsimp [C_row]; exact le_max_of_le_left h1
    have := mul_le_mul_of_nonneg_left this hCpos
    have := mul_le_mul_of_nonneg_right this (hφ_nonneg j hj)
    simpa [weight, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum2 := Finset.sum_le_sum hterm2
  have hfac' : (Finset.range K).sum (fun j => C_row * (weight j))
      = C_row * ((Finset.range K).sum (fun j => weight j)) := by
    classical
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Finset.mul_sum (s := Finset.range K) (a := C_row)
        (f := fun j => weight j)).symm
  have hsum2' : (Finset.range K).sum (fun j =>
      (C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹) * (weight j))
        ≤ C_row * ((Finset.range K).sum (fun j => weight j)) := by
    simpa [hfac', mul_comm, mul_left_comm, mul_assoc] using hsum2
  exact le_trans hsum <| by
    simpa [weight, C_row, mul_comm, mul_left_comm, mul_assoc] using hsum2'

end PoissonKernelDyadic
end RS
end RH
