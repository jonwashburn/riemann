import rh.Compat
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

/-! Minimal Poisson kernel helpers (inlined to avoid heavy dependencies). -/

/-- Cauchy/Poisson kernel: K_σ(x) = σ / (x^2 + σ^2). -/
@[simp] def Ksigma (σ x : ℝ) : ℝ := σ / (x^2 + σ^2)

lemma Ksigma_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Ksigma σ x := by
  unfold Ksigma
  have hden : 0 ≤ x^2 + σ^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact div_nonneg hσ hden

lemma Ksigma_mul_nonneg
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (t a b : ℝ) :
    0 ≤ Ksigma σ (t - a) * Ksigma τ (t - b) := by
  exact mul_nonneg (Ksigma_nonneg (σ := σ) (x := t - a) hσ)
                   (Ksigma_nonneg (σ := τ) (x := t - b) hτ)

lemma Ksigma_le_inv_sigma {σ x : ℝ} (hσ : 0 < σ) : Ksigma σ x ≤ 1 / σ := by
  unfold Ksigma
  have hden : σ ^ 2 ≤ x ^ 2 + σ ^ 2 := le_add_of_nonneg_left (sq_nonneg x)
  have hσ2pos : 0 < σ ^ 2 := by exact pow_pos hσ 2
  have hone : 1 / (x ^ 2 + σ ^ 2) ≤ 1 / σ ^ 2 := one_div_le_one_div_of_le hσ2pos hden
  have hmul := mul_le_mul_of_nonneg_left hone hσ.le
  have hEq : σ / σ ^ 2 = 1 / σ := by
    have hne : σ ≠ 0 := ne_of_gt hσ
    calc
      σ / σ ^ 2 = σ / (σ * σ) := by simp [pow_two]
      _ = (σ / σ) / σ := by simpa using (div_mul_eq_div_div σ σ σ)
      _ = 1 / σ := by simp [hne]
  exact (le_trans (by simpa [div_eq_mul_inv] using hmul) (le_of_eq hEq))

lemma Ksigma_le_sigma_div_sq {σ x : ℝ} (hσ : 0 ≤ σ) (hx : x ≠ 0) :
  Ksigma σ x ≤ σ / x^2 := by
  unfold Ksigma
  have hden : x ^ 2 ≤ x ^ 2 + σ ^ 2 := le_add_of_nonneg_right (sq_nonneg σ)
  have hxpos : 0 < x ^ 2 := by simpa using (sq_pos_of_ne_zero x hx)
  have hone : 1 / (x ^ 2 + σ ^ 2) ≤ 1 / x ^ 2 := one_div_le_one_div_of_le hxpos hden
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hone hσ

-- (aliases provided via the analysis shim if needed)

lemma Ksigma_add_bound_of_dyadic_sep
  {σ τ sep L : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hsep : 0 < sep) (hL : 0 < L)
  {a b : ℝ} {d : ℕ}
  (hsepAB : sep * (2 : ℝ) ^ d * L ≤ |a - b|) :
  Ksigma (σ + τ) (a - b)
    ≤ ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
  have hpos_prod : 0 < sep * (2 : ℝ) ^ d * L :=
    mul_pos (mul_pos hsep (pow_pos (by norm_num : (0 : ℝ) < 2) d)) hL
  have hxpos : 0 < |a - b| := lt_of_lt_of_le hpos_prod hsepAB
  have hxne : (a - b) ≠ 0 := sub_ne_zero.mpr (by
    have hne : |a - b| ≠ 0 := ne_of_gt hxpos
    exact by
      intro h; apply hne; simpa [h, abs_zero])
  have hbound :=
    Ksigma_le_sigma_div_sq (σ := σ + τ) (x := a - b) (add_pos hσ hτ).le hxne
  have hx2 : (a - b) ^ 2 ≥ (sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2) := by
    have hpos : 0 ≤ sep * 2 ^ d * L := by positivity
    have h_abs_le : |sep * 2 ^ d * L| ≤ |a - b| := by
      simpa [abs_of_nonneg hpos] using hsepAB
    have hsq' : (sep * 2 ^ d * L) ^ 2 ≤ (a - b) ^ 2 := by
      simpa using (RH.sq_le_sq.mpr (a := sep * 2 ^ d * L) (b := a - b) h_abs_le)
    have hx : sep ^ 2 * (2 ^ d) ^ 2 * L ^ 2 ≤ (a - b) ^ 2 := by
      simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hsq'
    have hx' : sep ^ 2 * 2 ^ (2 * d) * L ^ 2 ≤ (a - b) ^ 2 := by
      simpa [pow_mul, Nat.mul_comm] using hx
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx'
  have hx2_inv_le : 1 / (a - b) ^ 2 ≤
      (1 / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
    have hden2pos : 0 < (sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2) := by
      have h2pow : 0 < (2 : ℝ) ^ (2 * d) := pow_pos (by norm_num : (0 : ℝ) < 2) _
      exact mul_pos (mul_pos (pow_pos hsep 2) h2pow) (pow_pos hL 2)
    have hmono : 1 / (a - b) ^ 2 ≤ 1 / ((sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2)) :=
      one_div_le_one_div_of_le hden2pos hx2
    have hreshape : 1 / ((sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2))
        = (1 / (sep ^ 2 * L ^ 2)) * ((2 : ℝ) ^ (2 * d))⁻¹ := by
      -- algebraic reshaping without field_simp
      have : (sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2)
          = (sep ^ 2 * L ^ 2) * ((2 : ℝ) ^ (2 * d)) := by
        ring
      calc
        1 / ((sep ^ 2) * ((2 : ℝ) ^ (2 * d)) * (L ^ 2))
            = 1 / ((sep ^ 2 * L ^ 2) * ((2 : ℝ) ^ (2 * d))) := by simpa [this]
        _ = (1 / (sep ^ 2 * L ^ 2)) * ((2 : ℝ) ^ (2 * d))⁻¹ := by
          simp [one_div, inv_mul_eq_iff_eq_mul₀, mul_comm, mul_left_comm, mul_assoc]
    have hx' : 1 / (a - b) ^ 2 ≤ (1 / (sep ^ 2 * L ^ 2)) * ((2 : ℝ) ^ (2 * d))⁻¹ := by
      simpa [hreshape] using hmono
    have htwopow : (2 : ℝ) ^ (2 * d) = (4 : ℝ) ^ d := RH.two_pow_two_mul_eq_four_pow d
    simpa [htwopow] using hx'
  have hσt_pos : 0 < σ + τ := add_pos hσ hτ
  have : Ksigma (σ + τ) (a - b) ≤ (σ + τ) * (1 / (a - b) ^ 2) := by
    simpa [one_div, mul_comm] using hbound
  exact le_trans this <| by
    have := mul_le_mul_of_nonneg_left hx2_inv_le hσt_pos.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using this

lemma conv_upper_bound_4decay_of_sep
    {σ τ sep L : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hsep : 0 < sep) (hL : 0 < L)
  {a b : ℝ} {d : ℕ}
  (hconv : (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
    = Real.pi * Ksigma (σ + τ) (a - b))
    (hsepAB : sep * (2 : ℝ) ^ d * L ≤ |a - b|) :
    (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
    ≤ Real.pi * ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
  have hKs := Ksigma_add_bound_of_dyadic_sep (σ := σ) (τ := τ)
    (sep := sep) (L := L) hσ hτ hsep hL (a := a) (b := b) (d := d) hsepAB
  have hπpos : 0 ≤ Real.pi := Real.pi_pos.le
  have hπKs := mul_le_mul_of_nonneg_left hKs hπpos
  -- Rewrite the integral via the convolution identity, then apply the bound
  calc
    (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
        = Real.pi * Ksigma (σ + τ) (a - b) := hconv
    _ ≤ Real.pi * ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hπKs

-- move monotonicity lemma above first use
lemma Ksigma_pos {σ x : ℝ} (hσ : 0 < σ) : 0 < Ksigma σ x := by
  unfold Ksigma
  have hden : 0 < x ^ 2 + σ ^ 2 := by
    have : 0 ≤ x ^ 2 := sq_nonneg _
    have : 0 < x ^ 2 + σ ^ 2 := by
      have : 0 ≤ x ^ 2 := sq_nonneg _
      have : 0 < σ ^ 2 := pow_pos hσ 2
      linarith
    simpa using this
  exact div_pos hσ hden

lemma Ksigma_prod_integrable {σ τ a b : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    Integrable (fun t => Ksigma σ (t - a) * Ksigma τ (t - b)) := by
  -- Nonnegativity of the integrand
  have hf_nonneg : ∀ t, 0 ≤ Ksigma σ (t - a) * Ksigma τ (t - b) := by
    intro t; exact Ksigma_mul_nonneg (σ := σ) (τ := τ) hσ.le hτ.le t a b
  -- Constants giving uniform control of denominators
  let cσ : ℝ := min (1 : ℝ) (σ ^ 2)
  let cτ : ℝ := min (1 : ℝ) (τ ^ 2)
  have cσ_pos : 0 < cσ := lt_min_iff.mpr ⟨by norm_num, pow_pos hσ 2⟩
  have cτ_pos : 0 < cτ := lt_min_iff.mpr ⟨by norm_num, pow_pos hτ 2⟩
  have cσ_le_one : cσ ≤ 1 := min_le_left _ _
  have cσ_le_sq : cσ ≤ σ ^ 2 := min_le_right _ _
  have cτ_le_one : cτ ≤ 1 := min_le_left _ _
  have cτ_le_sq : cτ ≤ τ ^ 2 := min_le_right _ _
  -- Pointwise domination by a simple integrable function
  let C : ℝ := (σ * τ) * (cσ * cτ)⁻¹
  have hmajor : ∀ t, |σ / ((t - a) ^ 2 + σ ^ 2) * (τ / ((t - b) ^ 2 + τ ^ 2))|
      ≤ C * (1 + (t - a) ^ 2)⁻¹ := by
    intro t
    -- positivity of the product to remove abs via abs_of_nonneg
    have hdenσ : 0 < (t - a) ^ 2 + σ ^ 2 := by
      have : 0 ≤ (t - a) ^ 2 := sq_nonneg _
      have : 0 < σ ^ 2 := pow_pos hσ 2
      linarith
    have hdenτ : 0 < (t - b) ^ 2 + τ ^ 2 := by
      have : 0 ≤ (t - b) ^ 2 := sq_nonneg _
      have : 0 < τ ^ 2 := pow_pos hτ 2
      linarith
    have hprod_nonneg : 0 ≤ σ / ((t - a) ^ 2 + σ ^ 2) * (τ / ((t - b) ^ 2 + τ ^ 2)) := by
      have h1 : 0 ≤ σ / ((t - a) ^ 2 + σ ^ 2) := div_nonneg hσ.le hdenσ.le
      have h2 : 0 ≤ τ / ((t - b) ^ 2 + τ ^ 2) := div_nonneg hτ.le hdenτ.le
      exact mul_nonneg h1 h2
    -- step 1: bound each kernel separately
    have hσ_den_mono : cσ * (1 + (t - a) ^ 2) ≤ (t - a) ^ 2 + σ ^ 2 := by
      have hmul : cσ * (t - a) ^ 2 ≤ (t - a) ^ 2 := by
        simpa [one_mul] using
          (mul_le_mul_of_nonneg_right cσ_le_one (sq_nonneg _))
      have hsum : cσ + cσ * (t - a) ^ 2 ≤ σ ^ 2 + (t - a) ^ 2 :=
        add_le_add cσ_le_sq hmul
      simpa [mul_add, one_mul, add_comm, add_left_comm, add_assoc] using hsum
    have hKσ' : Ksigma σ (t - a) ≤ σ / (cσ * (1 + (t - a) ^ 2)) := by
      -- σ / ((t-a)^2 + σ^2) ≤ σ / (cσ * (1 + (t-a)^2))
      have hposB : 0 < cσ * (1 + (t - a) ^ 2) :=
        mul_pos cσ_pos (by linarith [sq_nonneg (t - a)])
      have :=
        (div_le_div_of_nonneg_left (by exact hσ.le) hposB hσ_den_mono)
      simpa [Ksigma, div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using this
    have hKτ' : Ksigma τ (t - b) ≤ τ / cτ := by
      -- τ / ((t-b)^2 + τ^2) ≤ τ / cτ since (t-b)^2 ≥ 0 and cτ ≤ τ^2
      have hden_mono : cτ ≤ (t - b) ^ 2 + τ ^ 2 := by
        have h0 : 0 ≤ (t - b) ^ 2 := sq_nonneg _
        have hτ2_le : τ ^ 2 ≤ (t - b) ^ 2 + τ ^ 2 := by
          exact le_add_of_nonneg_left h0
        exact le_trans cτ_le_sq hτ2_le
      have := div_le_div_of_nonneg_left (by exact hτ.le) cτ_pos hden_mono
      simpa [Ksigma, div_eq_mul_inv] using this
    -- step 2: multiply and simplify
    have hprod₁ : Ksigma σ (t - a) * Ksigma τ (t - b)
        ≤ (σ / (cσ * (1 + (t - a) ^ 2))) * Ksigma τ (t - b) := by
      exact mul_le_mul_of_nonneg_right hKσ' (Ksigma_nonneg (σ := τ) (x := t - b) hτ.le)
    have hprod : Ksigma σ (t - a) * Ksigma τ (t - b)
        ≤ (σ / (cσ * (1 + (t - a) ^ 2))) * (τ / cτ) := by
      exact le_trans hprod₁ (mul_le_mul_of_nonneg_left hKτ' (by positivity))
    have hbound :
        (σ / (cσ * (1 + (t - a) ^ 2))) * (τ / cτ)
          = C * (1 + (t - a) ^ 2)⁻¹ := by
      -- algebraic normalization, avoiding deep simp loops
      have hC : C = (σ / cσ) * (τ / cτ) := by
        simp [C, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      have : (σ / (cσ * (1 + (t - a) ^ 2))) * (τ / cτ)
          = ((σ / cσ) * (τ / cτ)) * (1 + (t - a) ^ 2)⁻¹ := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      simpa [this, hC]
      using rfl
    have hmaj' : Ksigma σ (t - a) * Ksigma τ (t - b)
        ≤ C * (1 + (t - a) ^ 2)⁻¹ :=
      le_trans hprod (by simpa [hbound])
    -- rewrite to the requested fraction shape, then add abs using nonnegativity
    have hfrac : σ / ((t - a) ^ 2 + σ ^ 2) * (τ / ((t - b) ^ 2 + τ ^ 2))
        ≤ C * (1 + (t - a) ^ 2)⁻¹ := by
      simpa [Ksigma, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmaj'
    have : |σ / ((t - a) ^ 2 + σ ^ 2) * (τ / ((t - b) ^ 2 + τ ^ 2))|
        ≤ C * (1 + (t - a) ^ 2)⁻¹ := by
      have hv : 0 ≤ σ / ((t - a) ^ 2 + σ ^ 2) * (τ / ((t - b) ^ 2 + τ ^ 2)) := hprod_nonneg
      simpa [abs_of_nonneg hv] using hfrac
    exact this
  -- Integrable majorant
  have hint : Integrable (fun t : ℝ => C * (1 + (t - a) ^ 2)⁻¹) := by
    simpa [sub_eq_add_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using (integrable_inv_one_add_sq.comp_sub_right a).const_mul C
  -- Measurability for the product (same as absolute value since nonnegative)
  have hmeas : AEStronglyMeasurable (fun t => Ksigma σ (t - a) * Ksigma τ (t - b)) := by
    -- The function is continuous (and hence measurable) since it's a composition
    -- of continuous functions: mul, div, sub, pow
    have hcont : Continuous (fun t : ℝ => Ksigma σ (t - a) * Ksigma τ (t - b)) := by
      apply Continuous.mul
      · unfold Ksigma
        apply Continuous.div
        · exact continuous_const
        · apply Continuous.add
          · apply Continuous.pow
            exact continuous_id.sub continuous_const
          · exact continuous_const
        · intro t; exact ne_of_gt (by
            have : 0 ≤ (t - a) ^ 2 := sq_nonneg _
            have : 0 < σ ^ 2 := pow_pos hσ 2
            linarith)
      · unfold Ksigma
        apply Continuous.div
        · exact continuous_const
        · apply Continuous.add
          · apply Continuous.pow
            exact continuous_id.sub continuous_const
          · exact continuous_const
        · intro t; exact ne_of_gt (by
            have : 0 ≤ (t - b) ^ 2 := sq_nonneg _
            have : 0 < τ ^ 2 := pow_pos hτ 2
            linarith)
    exact hcont.aestronglyMeasurable
  -- Prove integrability using the majorant
  have hf_ae : 0 ≤ᵐ[volume] (fun t => Ksigma σ (t - a) * Ksigma τ (t - b)) :=
    Filter.Eventually.of_forall hf_nonneg
  have hfg_ae : (fun t => Ksigma σ (t - a) * Ksigma τ (t - b))
      ≤ᵐ[volume] (fun t => C * (1 + (t - a) ^ 2)⁻¹) := by
    filter_upwards with t
    have hprod_nonneg : 0 ≤ Ksigma σ (t - a) * Ksigma τ (t - b) :=
      Ksigma_mul_nonneg (σ := σ) (τ := τ) hσ.le hτ.le t a b
    have h_eq_abs : |Ksigma σ (t - a) * Ksigma τ (t - b)| = Ksigma σ (t - a) * Ksigma τ (t - b) :=
      abs_of_nonneg hprod_nonneg
    rw [← h_eq_abs]
    simp only [Ksigma]
    exact hmajor t
  exact MeasureTheory.integrable_of_nonneg_of_le (μ := volume)
    hmeas hf_ae hfg_ae hint

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

def inDyadicAnnulus (c L : ℝ) (k : ℕ) (x : ℝ) : Prop :=
  (2 : ℝ) ^ k * L < |x - c| ∧ |x - c| ≤ (2 : ℝ) ^ (k + 1) * L

-- moved from the end of the file for earlier reuse
lemma sep_lower_bound (t a b : ℝ) : |t - b| ≥ |a - b| - |t - a| := by
  have : |a - b| ≤ |t - b| + |t - a| := by
    simpa [abs_sub_comm, add_comm] using (abs_sub_le a t b)
  exact (sub_le_iff_le_add).2 this

lemma sep_from_base_of_annulus
    {c L t x : ℝ} {k : ℕ}
    (hbase : |t - c| ≤ L) (hAnn : inDyadicAnnulus c L k x)
    (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) * L ≤ |t - x| := by
  have hLnonneg : 0 ≤ L := (abs_nonneg (t - c)).trans hbase
  have hsep : |t - x| ≥ |x - c| - |t - c| := by
    simpa [abs_sub_comm] using sep_lower_bound t c x
  have hx_lb : (2 : ℝ) ^ k * L ≤ |x - c| := le_of_lt hAnn.1
  have hx1 : (2 : ℝ) ^ k * L - |t - c| ≤ |t - x| := by
    have hx_above : (2 : ℝ) ^ k * L - |t - c| ≤ |x - c| - |t - c| :=
      sub_le_sub_right hx_lb _
    exact le_trans hx_above hsep
  have hx2 : (2 : ℝ) ^ k * L - L ≤ (2 : ℝ) ^ k * L - |t - c| :=
    sub_le_sub_left hbase _
  have : |t - x| ≥ (2 : ℝ) ^ k * L - L := le_trans hx2 hx1
  have hgeom : (2 : ℝ) ^ (k - 1) * L ≤ (2 : ℝ) ^ k * L - L := by
    have hrew : (2 : ℝ) ^ k * L - L = ((2 : ℝ) ^ k - 1) * L := by ring
    have hk1 : (2 : ℝ) ^ k - 1 ≥ (2 : ℝ) ^ (k - 1) := by
      have hkpos : 0 < k := by omega
      have hkpow : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
        have hkpos : 0 < k := by omega
        have h_eq : k = (k - 1) + 1 := by omega
        have h_eq_cast : (k : ℝ) = ((k - 1) + 1 : ℝ) := by
          norm_cast
          exact h_eq
        have : (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) := congr_arg (fun n : ℝ => (2 : ℝ) ^ n) h_eq_cast
        rw [this]
        rw [pow_add (2 : ℝ) (k - 1) 1, pow_one]
        ring
      have hnonneg : 0 ≤ (2 : ℝ) ^ (k - 1) := pow_nonneg (by norm_num) _
      have : (2 : ℝ) ^ (k - 1) - 1 ≥ 0 := by
        have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (k - 1)
        linarith
      have : 2 * (2 : ℝ) ^ (k - 1) - 1 ≥ (2 : ℝ) ^ (k - 1) := by linarith
      rw [← hkpow] at this
      exact this
    have hrw : (2 : ℝ) ^ (k - 1) * L ≤ ((2 : ℝ) ^ k - 1) * L :=
      mul_le_mul_of_nonneg_right hk1 hLnonneg
    simpa [hrew] using hrw
  exact le_trans hgeom this

lemma sep_between_annuli_gap_ge_two
    {c L x y : ℝ} {k j : ℕ}
    (hAnnX : inDyadicAnnulus c L k x)
    (hAnnY : inDyadicAnnulus c L j y)
    (hL : 0 < L) (hgap : 2 ≤ Nat.dist k j) :
    (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |x - y| := by
  have hkj := le_total k j
  rcases hkj with hkj | hjk
  · -- case k ≤ j
    have hdist : Nat.dist k j = j - k := Nat.dist_eq_sub_of_le hkj
    have hd2 : 2 ≤ j - k := by simpa [hdist] using hgap
    have hLnonneg : 0 ≤ L := le_of_lt hL
    -- |x - y| ≥ |y - c| - |x - c|
    have hsep : |x - y| ≥ |y - c| - |x - c| := by
      have := sep_lower_bound x c y
      simpa [abs_sub_comm] using this
    have hy_lb : (2 : ℝ) ^ j * L ≤ |y - c| := le_of_lt hAnnY.1
    have hx_ub : |x - c| ≤ (2 : ℝ) ^ (k + 1) * L := hAnnX.2
    have hdiff : (2 : ℝ) ^ j * L - (2 : ℝ) ^ (k + 1) * L ≤ |y - c| - |x - c| :=
      sub_le_sub hy_lb hx_ub
    have hcomb : (2 : ℝ) ^ j * L - (2 : ℝ) ^ (k + 1) * L ≤ |x - y| :=
      le_trans hdiff hsep
    -- show RHS ≥ 2^(j-1) L, then compare with target
    have hk1_lt_j : k + 1 < j := by
      -- From hd2: 2 ≤ j - k, we get j ≥ k + 2, so k + 1 < j
      have : k + 2 ≤ j := by
        have : j - k ≥ 2 := hd2
        omega
      omega
    have hk1_le_jpred : k + 1 ≤ j - 1 := Nat.le_pred_of_lt hk1_lt_j
    have hpow_mono : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (j - 1) :=
      pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) hk1_le_jpred
    have hdiff_ge : (2 : ℝ) ^ j * L - (2 : ℝ) ^ (j - 1) * L ≤ (2 : ℝ) ^ j * L - (2 : ℝ) ^ (k + 1) * L := by
      have := mul_le_mul_of_nonneg_right hpow_mono hLnonneg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_le_sub_left this ((2 : ℝ) ^ j * L))
    have h2j : (2 : ℝ) ^ j * L - (2 : ℝ) ^ (j - 1) * L = (2 : ℝ) ^ (j - 1) * L := by
      have : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1) * 2 := by
        have hpos : 0 < j := by omega
        have h_eq : j = (j - 1) + 1 := by
          have := Nat.succ_pred_eq_of_pos hpos
          rw [← this]
        have h_eq_cast : (j : ℝ) = ((j - 1) + 1 : ℝ) := by
          norm_cast
          exact h_eq
        have : (2 : ℝ) ^ j = (2 : ℝ) ^ ((j - 1) + 1) := congr_arg (fun n : ℝ => (2 : ℝ) ^ n) h_eq_cast
        rw [this]
        rw [pow_add (2 : ℝ) (j - 1) 1, pow_one]
        ring
      ring
    have hge_j1 : (2 : ℝ) ^ (j - 1) * L ≤ |x - y| :=
      le_trans (by simpa [h2j] using hdiff_ge) hcomb
    -- compare 2^(j-k-1) L to 2^(j-1) L
    have hmono_pow : (2 : ℝ) ^ (j - k - 1) ≤ (2 : ℝ) ^ (j - 1) := by
      have : j - k - 1 ≤ j - 1 := Nat.sub_le_sub_right hkj 1
      exact pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) this
    have : (2 : ℝ) ^ (j - k - 1) * L ≤ (2 : ℝ) ^ (j - 1) * L :=
      mul_le_mul_of_nonneg_right hmono_pow hLnonneg
    have : (2 : ℝ) ^ (j - k - 1) * L ≤ |x - y| := le_trans this hge_j1
    -- target: (1/2) * 2^(j-k) * L ≤ |x - y|
    -- we have: 2^(j-k-1) * L ≤ |x - y|
    -- need: (1/2) * 2^(j-k) = 2^(j-k-1)
    have htarget : (1 / 2 : ℝ) * (2 : ℝ) ^ (j - k) * L = (2 : ℝ) ^ (j - k - 1) * L := by
      have : (1 / 2 : ℝ) * (2 : ℝ) ^ (j - k) = (2 : ℝ) ^ (j - k - 1) := by
        have : (2 : ℝ) ^ (j - k) = 2 * (2 : ℝ) ^ (j - k - 1) := by
          have hpos : 0 < j - k - 1 := by
            have : 2 ≤ j - k := hd2
            omega
          have h_eq : j - k = (j - k - 1) + 1 := Nat.succ_pred_eq_of_pos hpos
          have h_eq_cast : (j - k : ℝ) = ((j - k - 1) + 1 : ℝ) := by
            norm_cast
            exact h_eq
          have : (2 : ℝ) ^ (j - k) = (2 : ℝ) ^ ((j - k - 1) + 1) := congr_arg (fun n : ℝ => (2 : ℝ) ^ n) h_eq_cast
          rw [this]
          rw [pow_add (2 : ℝ) (j - k - 1) 1, pow_one]
          ring
        ring
      rw [this]
    rw [htarget] at this
    exact this
  · -- case j ≤ k: explicit symmetric case (no recursion)
    have hdist : Nat.dist k j = k - j := by rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hjk]
    have hd2 : 2 ≤ k - j := by simpa [hdist] using hgap
    have hLnonneg : 0 ≤ L := le_of_lt hL
    -- |x - y| ≥ |x - c| - |y - c| (symmetric to the k ≤ j case)
    have hsep : |x - y| ≥ |x - c| - |y - c| := by
      have := sep_lower_bound y c x
      simpa [abs_sub_comm] using this
    have hx_lb : (2 : ℝ) ^ k * L ≤ |x - c| := le_of_lt hAnnX.1
    have hy_ub : |y - c| ≤ (2 : ℝ) ^ (j + 1) * L := hAnnY.2
    have hdiff : (2 : ℝ) ^ k * L - (2 : ℝ) ^ (j + 1) * L ≤ |x - c| - |y - c| :=
      sub_le_sub hx_lb hy_ub
    have hcomb : (2 : ℝ) ^ k * L - (2 : ℝ) ^ (j + 1) * L ≤ |x - y| :=
      le_trans hdiff hsep
    -- show RHS ≥ 2^(k-1) L, then compare with target
    have hj1_lt_k : j + 1 < k := by
      -- From hd2: 2 ≤ k - j, we get k ≥ j + 2, so j + 1 < k
      have : j + 2 ≤ k := by
        have : k - j ≥ 2 := hd2
        omega
      omega
    have hj1_le_kpred : j + 1 ≤ k - 1 := Nat.le_pred_of_lt hj1_lt_k
    have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (k - 1) :=
      pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) hj1_le_kpred
    have hdiff_ge : (2 : ℝ) ^ k * L - (2 : ℝ) ^ (k - 1) * L ≤ (2 : ℝ) ^ k * L - (2 : ℝ) ^ (j + 1) * L := by
      have := mul_le_mul_of_nonneg_right hpow_mono hLnonneg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_le_sub_left this ((2 : ℝ) ^ k * L))
    have h2k : (2 : ℝ) ^ k * L - (2 : ℝ) ^ (k - 1) * L = (2 : ℝ) ^ (k - 1) * L := by
      have : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
        have hpos : 0 < k := by omega
        have h_eq : k = (k - 1) + 1 := by omega
        have h_eq_cast : (k : ℝ) = ((k - 1) + 1 : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one, Nat.cast_sub (Nat.le_of_succ_le hpos), h_eq]
        have : (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) := congr_arg (fun n : ℝ => (2 : ℝ) ^ n) h_eq_cast
        rw [this]
        rw [pow_add (2 : ℝ) (k - 1) 1, pow_one]
        ring
      ring
    have hge_k1 : (2 : ℝ) ^ (k - 1) * L ≤ |x - y| :=
      le_trans (by simpa [h2k] using hdiff_ge) hcomb
    -- compare 2^(k-j-1) L to 2^(k-1) L
    have hmono_pow : (2 : ℝ) ^ (k - j - 1) ≤ (2 : ℝ) ^ (k - 1) := by
      have : k - j - 1 ≤ k - 1 := Nat.sub_le_sub_right hjk 1
      exact pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) this
    have : (2 : ℝ) ^ (k - j - 1) * L ≤ (2 : ℝ) ^ (k - 1) * L :=
      mul_le_mul_of_nonneg_right hmono_pow hLnonneg
    have : (2 : ℝ) ^ (k - j - 1) * L ≤ |x - y| := le_trans this hge_k1
    -- target: (1/2) * 2^(k-j) * L ≤ |x - y|
    -- we have: 2^(k-j-1) * L ≤ |x - y|
    -- need: (1/2) * 2^(k-j) = 2^(k-j-1)
    have htarget : (1 / 2 : ℝ) * (2 : ℝ) ^ (k - j) * L = (2 : ℝ) ^ (k - j - 1) * L := by
      have : (1 / 2 : ℝ) * (2 : ℝ) ^ (k - j) = (2 : ℝ) ^ (k - j - 1) := by
        have : (2 : ℝ) ^ (k - j) = 2 * (2 : ℝ) ^ (k - j - 1) := by
          have hpos : 0 < k - j - 1 := by
            have : 2 ≤ k - j := hd2
            omega
          have h_eq : k - j = (k - j - 1) + 1 := Nat.succ_pred_eq_of_pos hpos
          have h_eq_cast : (k - j : ℝ) = ((k - j - 1) + 1 : ℝ) := by
            norm_cast
            exact h_eq
          have : (2 : ℝ) ^ (k - j) = (2 : ℝ) ^ ((k - j - 1) + 1) := congr_arg (fun n : ℝ => (2 : ℝ) ^ n) h_eq_cast
          rw [this]
          rw [pow_add (2 : ℝ) (k - j - 1) 1, pow_one]
          ring
        ring
      rw [this]
    rw [htarget] at this
    -- Now need to connect to Nat.dist_comm
    have hdist_equiv : (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L = (1 / 2 : ℝ) * (2 : ℝ) ^ (k - j) * L := by
      rw [hdist]
    rw [← hdist_equiv, ← htarget] at this
    -- abs_sub_comm gives |x - y| = |y - x|
    rw [abs_sub_comm]
    exact this

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
    have hidentity := hconv k j
    -- monotonicity of restriction using integrability, obtained via the identity hidentity
    have hfi : Integrable (fun t => Ksigma σ (t - a k) * Ksigma τ (t - b j)) :=
      Ksigma_prod_integrable (σ := σ) (τ := τ) (a := a k) (b := b j) hσ hτ
    have hrest := integral_restrict_mono_of_nonneg
      (f := fun t => Ksigma σ (t - a k) * Ksigma τ (t - b j))
      hnonneg_integrand S hS hfi
    by_cases hcase : 2 ≤ Nat.dist k j
    · have hsep : ((1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L) ≤ |a k - b j| :=
        sep_between_annuli_gap_ge_two (c := c) (L := L) (x := a k) (y := b j)
          (hAnnX := ha k) (hAnnY := hb j) hL hcase
      have := conv_upper_bound_4decay_of_sep (σ := σ) (τ := τ)
        (sep := (1 / 2 : ℝ)) (L := L) hσ hτ (by norm_num) hL
        (a := a k) (b := b j) (d := Nat.dist k j) (hconv := hidentity)
        (hsepAB := hsep)
      have hx : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_far * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ :=
        le_trans hrest this
      have hφ_nonneg : 0 ≤ ((4 : ℝ) ^ j)⁻¹ * (nu j) :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) (hnu_nonneg j)
      have hCrow_ge : C_far ≤ C_row := le_max_left _ _
      have : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ :=
        le_trans hx <|
          by
            have := mul_le_mul_of_nonneg_right hCrow_ge
              (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
            simpa [C_far, C_row, mul_comm, mul_left_comm, mul_assoc] using this
      exact mul_le_mul_of_nonneg_right this hφ_nonneg
    · have hle : Nat.dist k j ≤ 1 := Nat.lt_succ_iff.mp (lt_of_not_ge hcase)
      have hWhole :
          (∫ t, Ksigma σ (t - a k) * Ksigma τ (t - b j))
            ≤ Real.pi / (σ + τ) := by
        rw [hidentity]
        have : Ksigma (σ + τ) (a k - b j) ≤ 1 / (σ + τ) :=
          Ksigma_le_inv_sigma (σ := σ + τ) (x := a k - b j) (add_pos hσ hτ)
        have : Real.pi * Ksigma (σ + τ) (a k - b j) ≤ Real.pi * (1 / (σ + τ)) :=
          mul_le_mul_of_nonneg_left this Real.pi_pos.le
        simpa [one_div] using this
      have hRestr_le := le_trans hrest hWhole
      have hCrow_ge : Real.pi / (σ + τ)
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
        have hdec_ge : ((4 : ℝ) ^ (Nat.dist k j))⁻¹ ≥ (4 : ℝ)⁻¹ := by
          by_cases h0 : Nat.dist k j = 0
          · -- if dist = 0, then (4^0)⁻¹ = 1 ≥ 1/4 = 4⁻¹
            have : (4 : ℝ) ^ 0 = (1 : ℝ) := by simp
            have : ((4 : ℝ) ^ 0)⁻¹ = (1 : ℝ) := by simp [this]
            have : (1 : ℝ) ≥ (4 : ℝ)⁻¹ := by norm_num
            simpa [h0, this]
          · -- if dist = 1, then (4^1)⁻¹ = 1/4 = 4⁻¹
            have h1 : Nat.dist k j = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0))
            simpa [h1] using (le_of_eq (by simp : ((4 : ℝ) ^ 1)⁻¹ = (4 : ℝ)⁻¹))
        have hmono : (4 : ℝ)⁻¹ ≤ ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
          simpa using hdec_ge
        have hCpos : 0 ≤ 4 * (Real.pi / (σ + τ)) := by
          have : 0 ≤ Real.pi / (σ + τ) :=
            div_nonneg Real.pi_pos.le (add_nonneg hσ.le hτ.le)
          exact mul_nonneg (by norm_num) this
        have : (Real.pi / (σ + τ)) ≤ C_near * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
          refine le_trans ?_ (mul_le_mul_of_nonneg_left hmono hCpos)
          have : (1 : ℝ) ≤ 4 * (4 : ℝ)⁻¹ := by norm_num
          have hπpos : 0 ≤ Real.pi / (σ + τ) :=
            div_nonneg Real.pi_pos.le (add_nonneg hσ.le hτ.le)
          simpa [C_near, mul_comm, mul_left_comm, mul_assoc]
            using mul_le_mul_of_nonneg_left this hπpos
        have hCnear_le : C_near ≤ C_row := le_max_right _ _
        have hdec_nonneg : 0 ≤ ((4 : ℝ) ^ (Nat.dist k j))⁻¹ :=
          inv_nonneg.mpr (pow_nonneg (by norm_num) _)
        have hscale := mul_le_mul_of_nonneg_right hCnear_le hdec_nonneg
        exact le_trans this hscale
      have hφ_nonneg : 0 ≤ ((4 : ℝ) ^ j)⁻¹ * (nu j) :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) (hnu_nonneg j)
      have : (∫ t in S, Ksigma σ (t - a k) * Ksigma τ (t - b j))
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ :=
        le_trans hRestr_le hCrow_ge
      exact mul_le_mul_of_nonneg_right this hφ_nonneg
  have hsum := Finset.sum_le_sum hterm
  have hdec_le_one : ∀ j ∈ Finset.range K,
      ((4 : ℝ) ^ (Nat.dist k j))⁻¹ ≤ 1 := by
    intro j hj
    have hge : (1 : ℝ) ≤ (4 : ℝ) ^ (Nat.dist k j) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) _
    have : 1 / (4 : ℝ) ^ (Nat.dist k j) ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) hge
    simpa [one_div] using this
  have hφ_nonneg : ∀ j ∈ Finset.range K,
      0 ≤ ((4 : ℝ) ^ j)⁻¹ * (nu j) := by
    intro j hj; exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) (hnu_nonneg j)
  have hterm2 : ∀ j ∈ Finset.range K,
      (C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹) * (((4 : ℝ) ^ j)⁻¹ * (nu j))
      ≤ C_row * (((4 : ℝ) ^ j)⁻¹ * (nu j)) := by
    intro j hj
    have := hdec_le_one j hj
    have hCpos : 0 ≤ C_row := by
      have h1 : 0 ≤ C_far := by
        have hdenpos : 0 < ((1 / 2 : ℝ) ^ 2 * L ^ 2) := by
          have : 0 < (1 / 2 : ℝ) := by norm_num
          have h1 : 0 < (1 / 2 : ℝ) ^ 2 := pow_pos this 2
          have h2 : 0 < L ^ 2 := pow_pos hL 2
          exact mul_pos h1 h2
        exact mul_nonneg Real.pi_pos.le
          (div_nonneg (add_nonneg hσ.le hτ.le) (le_of_lt hdenpos))
      dsimp [C_row]; exact le_max_of_le_left h1
    have := mul_le_mul_of_nonneg_left this hCpos
    have := mul_le_mul_of_nonneg_right this (hφ_nonneg j hj)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hsum2 := Finset.sum_le_sum hterm2
  have hfac : (Finset.range K).sum
      (fun j => C_row * (((4 : ℝ) ^ j)⁻¹ * (nu j)))
      = C_row * ((Finset.range K).sum (fun j => ((4 : ℝ) ^ j)⁻¹ * (nu j))) := by
    classical
    simpa using
      (Finset.mul_sum (s := Finset.range K) (a := C_row)
        (f := fun j => ((4 : ℝ) ^ j)⁻¹ * (nu j))).symm
  -- hsum2: ∑ j (C_row * (4^dist k j)⁻¹ * (4^j)⁻¹ * nu j) ≤ ∑ j (C_row * (4^j)⁻¹ * nu j)
  -- hfac: ∑ j (C_row * (4^j)⁻¹ * nu j) = C_row * ∑ j ((4^j)⁻¹ * nu j)
  -- target: ∑ j (C_row * (4^dist k j)⁻¹ * (4^j)⁻¹ * nu j) ≤ C_row * ∑ j ((4^j)⁻¹ * nu j)
  exact le_trans hsum (by rw [← hfac]; exact hsum2)

end PoissonKernelDyadic
end RS
end RH
