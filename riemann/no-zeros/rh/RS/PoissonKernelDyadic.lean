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

/-! Auxiliary monotonicity facts for powers of constants ≥ 1. -/

lemma one_le_const_pow {a : ℝ} (ha : 1 ≤ a) : ∀ n : ℕ, (1 : ℝ) ≤ a ^ n := by
  intro n
  induction' n with n ih
  · simp
  · have ha_nonneg : 0 ≤ a := le_trans (by norm_num) ha
    have hn_nonneg : 0 ≤ a ^ n := pow_nonneg ha_nonneg _
    have hstep : (1 : ℝ) * (1 : ℝ) ≤ a * a ^ n :=
      mul_le_mul ha ih (by norm_num) ha_nonneg
    simpa [pow_succ, mul_comm] using hstep

lemma one_le_two_pow (n : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ n :=
  one_le_const_pow (by norm_num) n

lemma one_le_four_pow (n : ℕ) : (1 : ℝ) ≤ (4 : ℝ) ^ n :=
  one_le_const_pow (by norm_num) n

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
  calc
    (∫ t, Ksigma σ (t - a) * Ksigma τ (t - b))
        = Real.pi * Ksigma (σ + τ) (a - b) := hconv
    _ ≤ Real.pi * ((σ + τ) / (sep ^ 2 * L ^ 2)) * ((4 : ℝ) ^ d)⁻¹ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hπKs

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
  -- Inverse-monotonicity bounds
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
  -- Pointwise domination by a simple integrable function
  let C : ℝ := (σ * τ) * (cσ * cτ)⁻¹
  have hmajor : ∀ t, |Ksigma σ (t - a) * Ksigma τ (t - b)| ≤ C * (1 + (t - a) ^ 2)⁻¹ := by
    intro t
    have hnonneg := hf_nonneg t
    have hEq : Ksigma σ (t - a) * Ksigma τ (t - b)
        = (σ * τ) * (((t - a) ^ 2 + σ ^ 2)⁻¹ * ((t - b) ^ 2 + τ ^ 2)⁻¹) := by
      simp [Ksigma, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hA := invA t
    have hB := invB t
    have hmul := mul_le_mul hA hB (by positivity) (by positivity)
    have hstep1 : Ksigma σ (t - a) * Ksigma τ (t - b)
        ≤ (σ * τ) * ((cσ * (1 + (t - a) ^ 2))⁻¹ * (cτ * (1 + (t - b) ^ 2))⁻¹) := by
      simpa [hEq, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hmul (by positivity)
    have hsep : (cσ * (1 + (t - a) ^ 2))⁻¹ * (cτ * (1 + (t - b) ^ 2))⁻¹
        = (cσ * cτ)⁻¹ * (1 + (t - a) ^ 2)⁻¹ * (1 + (t - b) ^ 2)⁻¹ := by
      have h1 : (cσ * (1 + (t - a) ^ 2))⁻¹ = cσ⁻¹ * (1 + (t - a) ^ 2)⁻¹ := by
        by_cases hcσ : cσ = 0
        · simp [hcσ]
        · field_simp [hcσ, one_div, mul_comm, mul_left_comm, mul_assoc]
      have h2 : (cτ * (1 + (t - b) ^ 2))⁻¹ = cτ⁻¹ * (1 + (t - b) ^ 2)⁻¹ := by
        by_cases hcτ : cτ = 0
        · simp [hcτ]
        · field_simp [hcτ, one_div, mul_comm, mul_left_comm, mul_assoc]
      have : cσ⁻¹ * (1 + (t - a) ^ 2)⁻¹ * (cτ⁻¹ * (1 + (t - b) ^ 2)⁻¹)
          = (cσ * cτ)⁻¹ * (1 + (t - a) ^ 2)⁻¹ * (1 + (t - b) ^ 2)⁻¹ := by
        by_cases hcσ : cσ = 0 <;> by_cases hcτ : cτ = 0
        · simp [hcσ, hcτ]
        · simp [hcσ, hcτ, one_div, mul_comm, mul_left_comm, mul_assoc]
      simpa [h1, h2, mul_comm, mul_left_comm, mul_assoc] using this
    have hdrop : (1 + (t - b) ^ 2)⁻¹ ≤ (1 : ℝ) := by
      have : (1 : ℝ) ≤ 1 + (t - b) ^ 2 := by linarith [sq_nonneg (t - b)]
      have h1 : 0 < (1 : ℝ) := by norm_num
      simpa [one_div] using RH.inv_le_inv_of_le h1 this
    have hC_nonneg : 0 ≤ (σ * τ) * (cσ * cτ)⁻¹ * (1 + (t - a) ^ 2)⁻¹ := by positivity
    have hfinal : Ksigma σ (t - a) * Ksigma τ (t - b)
        ≤ (σ * τ) * (cσ * cτ)⁻¹ * (1 + (t - a) ^ 2)⁻¹ := by
      have := mul_le_mul_of_nonneg_left hdrop hC_nonneg
      have := le_trans (le_of_eq (by ring_nf :
        (σ * τ) * ((cσ * (1 + (t - a) ^ 2))⁻¹ * (cτ * (1 + (t - b) ^ 2))⁻¹)
          = (σ * τ) * (cσ * cτ)⁻¹ * (1 + (t - a) ^ 2)⁻¹ * (1 + (t - b) ^ 2)⁻¹))
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using this)
      exact this
    have : |Ksigma σ (t - a) * Ksigma τ (t - b)|
        = Ksigma σ (t - a) * Ksigma τ (t - b) := by
      simpa [abs_of_nonneg (hnonneg)]
    simpa [this, mul_comm, mul_left_comm, mul_assoc] using
      (le_trans hstep1 <| by
        simpa [hsep, mul_comm, mul_left_comm, mul_assoc] using hfinal)
  -- Integrable majorant
  have hint : Integrable (fun t : ℝ => C * (1 + (t - a) ^ 2)⁻¹) := by
    simpa [sub_eq_add_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using (integrable_inv_one_add_sq.comp_sub_right a).const_mul C
  exact MeasureTheory.integrable_of_nonneg_of_le (μ := volume)
    (f := fun t => |Ksigma σ (t - a) * Ksigma τ (t - b)|)
    (g := fun t => C * (1 + (t - a) ^ 2)⁻¹)
    (by
      have : ∀ t, 0 ≤ |Ksigma σ (t - a) * Ksigma τ (t - b)| := by intro t; exact abs_nonneg _
      exact Filter.Eventually.of_forall this)
    (by
      have : ∀ t, |Ksigma σ (t - a) * Ksigma τ (t - b)| ≤ C * (1 + (t - a) ^ 2)⁻¹ := by
        intro t; simpa [abs_of_nonneg (hf_nonneg t)] using hmajor t
      exact Filter.Eventually.of_forall this)
    hint

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
        have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := one_le_two_pow (k - 1)
        linarith [hge]
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
      have : Nat.dist k j = j - k := Nat.dist_eq_sub_of_le hkj
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
      have hkpos : 1 ≤ k - j := (by
        have h12 : (1 : ℕ) ≤ 2 := by decide
        exact le_trans h12 hm)
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
      have hge : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_two_pow j
      have := mul_le_mul_of_nonneg_left hgeom hge
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
    · have hsep : (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * L ≤ |a k - b j| :=
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
        have : Ksigma (σ + τ) (a k - b j) ≤ 1 / (σ + τ) :=
          Ksigma_le_inv_sigma (σ := σ + τ) (x := a k - b j) (add_pos hσ hτ)
        simpa [hidentity, mul_comm, mul_left_comm, mul_assoc]
          using mul_le_mul_of_nonneg_left this Real.pi_pos.le
      have hRestr_le := le_trans hrest hWhole
      have hCrow_ge : Real.pi / (σ + τ)
          ≤ C_row * ((4 : ℝ) ^ (Nat.dist k j))⁻¹ := by
        have hdec_ge : ((4 : ℝ) ^ (Nat.dist k j))⁻¹ ≥ (4 : ℝ)⁻¹ := by
          by_cases h0 : Nat.dist k j = 0
          · simpa [h0] using (by
              have : (4 : ℝ) ^ 0 = (1 : ℝ) := by simp
              simpa [this, one_div] : ((4 : ℝ) ^ 0)⁻¹ = (4 : ℝ)⁻¹)
          · have h1 : Nat.dist k j = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0))
            simpa [h1, one_div] using (le_of_eq (by simp : ((4 : ℝ) ^ 1)⁻¹ = (4 : ℝ)⁻¹))
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
        exact le_trans (le_max_right _ _) this
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
      simpa using one_le_four_pow (Nat.dist k j)
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
    simpa using (Finset.mul_sum (s := Finset.range K) (a := C_row)
      (f := fun j => ((4 : ℝ) ^ j)⁻¹ * (nu j)))
  exact le_trans hsum <|
    by simpa [hfac, C_row, mul_comm, mul_left_comm, mul_assoc] using hsum2

lemma sep_lower_bound (t a b : ℝ) : |t - b| ≥ |a - b| - |t - a| := by
  have : |a - b| ≤ |t - b| + |t - a| := by
    simpa [abs_sub_comm, add_comm] using (abs_sub_le a t b)
  exact (sub_le_iff_le_add).2 this

end PoissonKernelDyadic
end RS
end RH
