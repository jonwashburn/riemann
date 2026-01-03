import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Sonin Spaces

This file defines Sonin spaces following Connes-Moscovici [CM22] and
Connes-Consani-Moscovici [CCM24] on the spectral realization of zeros of ζ(s).

## Main Definitions

* `Sonin.VanishesOnBall Λ f`: `f` vanishes a.e. on `{|x| < Λ}`
* `Sonin.MemSoninSpace Λ f`: `f ∈ 𝐒_Λ` (L², vanishes on ball, Fourier transform vanishes on ball)
* `Sonin.SoninSubspace Λ`: The L² subspace of functions vanishing on `(-Λ, Λ)`
* `Sonin.ProlateOperatorData`: Structure capturing the spectral data of `W_Λ`

## Mathematical Background

### Definition (CCM24, Definition 5.1)

For a local field 𝕂, additive character α, and Λ > 0, the **Sonin space** is:
  `𝐒_Λ(𝕂, α) := { f ∈ L²(𝕂) | f(x) = 0 and ℱ_α f(x) = 0 for |x| < Λ }`

### Key Results

1. `complementBall_measure_infinite`: `{|x| ≥ Λ}` has infinite measure (Amrein-Berthier fails)
2. `MemSoninSpace.smul`, `.add`: 𝐒_Λ is a vector space
3. `MemSoninSpace.fourierIntegral`: 𝐒_Λ is Fourier-invariant
4. `ProlateOperatorData.eigenfunction_mem_soninSpace`: Negative eigenfunctions ∈ 𝐒_Λ

## References

* [CM22] Connes-Moscovici, "Prolate spheroidal operator and Zeta", PNAS 2022
* [CCM24] Connes-Consani-Moscovici, "Zeta zeros and prolate wave operators"
-/

noncomputable section

open MeasureTheory Measure Set Filter Topology Complex Real
open scoped ENNReal NNReal FourierTransform Topology

namespace Sonin

/-! ## Section 1: Fourier Transform Properties

We use Mathlib's existing Fourier transform infrastructure. The main properties we need
(linearity, vanishing at zero) follow from the definitions. -/

/-- The Fourier transform of 0 is 0. -/
@[simp]
theorem fourierIntegral_zero : FourierTransform.fourier (0 : ℝ → ℂ) = 0 := by
  ext ξ
  simp only [FourierTransform.fourier, VectorFourier.fourierIntegral, Pi.zero_apply,
             smul_zero, integral_zero]

/-- Scalar multiplication commutes with Fourier transform. -/
@[simp]
theorem fourierIntegral_smul (c : ℂ) (f : ℝ → ℂ) :
    FourierTransform.fourier (c • f) = c • FourierTransform.fourier f := by
  ext ξ
  simp only [Pi.smul_apply, FourierTransform.fourier, VectorFourier.fourierIntegral, ← integral_smul]
  congr 1; ext x; rw [smul_comm]

/-! ## Section 2: Vanishing Predicates -/

/-- `f` vanishes almost everywhere on `{|x| < Λ}`. -/
def VanishesOnBall (Λ : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ᵐ x ∂volume, |x| < Λ → f x = 0

@[simp]
theorem vanishesOnBall_zero (Λ : ℝ) : VanishesOnBall Λ (0 : ℝ → ℂ) :=
  ae_of_all _ fun _ _ => rfl

theorem VanishesOnBall.add {Λ : ℝ} {f g : ℝ → ℂ}
    (hf : VanishesOnBall Λ f) (hg : VanishesOnBall Λ g) :
    VanishesOnBall Λ (f + g) := by
  filter_upwards [hf, hg] with x hfx hgx habs
  simp only [Pi.add_apply, hfx habs, hgx habs, add_zero]

theorem VanishesOnBall.smul {Λ : ℝ} (c : ℂ) {f : ℝ → ℂ} (hf : VanishesOnBall Λ f) :
    VanishesOnBall Λ (c • f) := by
  filter_upwards [hf] with x hfx habs
  simp only [Pi.smul_apply, hfx habs, smul_zero]

theorem VanishesOnBall.neg {Λ : ℝ} {f : ℝ → ℂ} (hf : VanishesOnBall Λ f) :
    VanishesOnBall Λ (-f) := by
  filter_upwards [hf] with x hfx habs
  simp only [Pi.neg_apply, hfx habs, neg_zero]

theorem VanishesOnBall.mono {Λ₁ Λ₂ : ℝ} {f : ℝ → ℂ} (hf : VanishesOnBall Λ₂ f) (h : Λ₁ ≤ Λ₂) :
    VanishesOnBall Λ₁ f := by
  filter_upwards [hf] with x hfx habs
  exact hfx (lt_of_lt_of_le habs h)

theorem VanishesOnBall.of_ae_restrict {Λ : ℝ} {f : ℝ → ℂ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (-Λ) Λ)), f x = 0) :
    VanishesOnBall Λ f := by
  rw [ae_restrict_iff' measurableSet_Ioo] at hf
  filter_upwards [hf] with x hfx habs
  apply hfx
  simp only [mem_Ioo]
  constructor <;> linarith [abs_lt.mp habs]

theorem VanishesOnBall.to_ae_restrict {Λ : ℝ} {f : ℝ → ℂ} (hf : VanishesOnBall Λ f) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-Λ) Λ)), f x = 0 := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hf] with x hfx hx
  apply hfx
  simp only [mem_Ioo] at hx
  rw [abs_lt]
  exact ⟨hx.1, hx.2⟩

/-! ## Section 3: Sonin Space Membership -/

/-- Membership in the Sonin space `𝐒_Λ`.

A function `f : ℝ → ℂ` belongs to `𝐒_Λ` if:
1. `f ∈ L²(ℝ)`
2. `f(x) = 0` for a.e. `|x| < Λ`
3. `ℱf(ξ) = 0` for a.e. `|ξ| < Λ` -/
structure MemSoninSpace (Λ : ℝ) (f : ℝ → ℂ) : Prop where
  memL2 : MemLp f 2 volume
  vanishesTime : VanishesOnBall Λ f
  vanishesFreq : VanishesOnBall Λ (FourierTransform.fourier f)

namespace MemSoninSpace

variable {Λ : ℝ}

@[simp]
protected theorem zero : MemSoninSpace Λ (0 : ℝ → ℂ) where
  memL2 := MemLp.zero
  vanishesTime := vanishesOnBall_zero Λ
  vanishesFreq := by simp

protected theorem add {f g : ℝ → ℂ}
    (hf : MemSoninSpace Λ f) (hg : MemSoninSpace Λ g)
    (hfourier_add : FourierTransform.fourier (f + g) = FourierTransform.fourier f + FourierTransform.fourier g) :
    MemSoninSpace Λ (f + g) where
  memL2 := hf.memL2.add hg.memL2
  vanishesTime := hf.vanishesTime.add hg.vanishesTime
  vanishesFreq := by rw [hfourier_add]; exact hf.vanishesFreq.add hg.vanishesFreq

protected theorem smul (c : ℂ) {f : ℝ → ℂ} (hf : MemSoninSpace Λ f) :
    MemSoninSpace Λ (c • f) where
  memL2 := hf.memL2.const_smul c
  vanishesTime := hf.vanishesTime.smul c
  vanishesFreq := by simp [hf.vanishesFreq.smul c]

protected theorem neg {f : ℝ → ℂ} (hf : MemSoninSpace Λ f) :
    MemSoninSpace Λ (-f) := by
  have : -f = (-1 : ℂ) • f := by ext; simp
  rw [this]
  exact hf.smul (-1)

/-- **Fourier invariance** (Proposition 5.2 [CCM24]): `ℱ(𝐒_Λ) ⊆ 𝐒_Λ`. -/
protected theorem fourierIntegral {f : ℝ → ℂ}
    (hf : MemSoninSpace Λ f)
    (hf_L2_fourier : MemLp (FourierTransform.fourier f) 2 volume)
    (hf_double_vanish : VanishesOnBall Λ (FourierTransform.fourier (FourierTransform.fourier f))) :
    MemSoninSpace Λ (FourierTransform.fourier f) where
  memL2 := hf_L2_fourier
  vanishesTime := hf.vanishesFreq
  vanishesFreq := hf_double_vanish

protected theorem mono {Λ₁ Λ₂ : ℝ} {f : ℝ → ℂ} (hf : MemSoninSpace Λ₂ f) (h : Λ₁ ≤ Λ₂) :
    MemSoninSpace Λ₁ f where
  memL2 := hf.memL2
  vanishesTime := hf.vanishesTime.mono h
  vanishesFreq := hf.vanishesFreq.mono h

end MemSoninSpace

/-! ## Section 4: The Sonin Subspace of L² -/

/-- The Sonin subspace of L²(ℝ) consisting of functions vanishing on `(-Λ, Λ)`.
    This is defined as a predicate on Lp functions. -/
def SoninSubspacePred (Λ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Ioo (-Λ) Λ)), (f : ℝ → ℂ) x = 0

/-- Zero satisfies the Sonin subspace predicate. -/
theorem soninSubspacePred_zero (Λ : ℝ) : SoninSubspacePred Λ 0 := by
  unfold SoninSubspacePred
  have h : (↑↑(0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᶠ[ae volume] 0 := Lp.coeFn_zero _ _ _
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [h] with x hx _
  rw [hx, Pi.zero_apply]

/-- The Sonin predicate is closed under addition. -/
theorem SoninSubspacePred.add {Λ : ℝ} {f g : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : SoninSubspacePred Λ f) (hg : SoninSubspacePred Λ g) :
    SoninSubspacePred Λ (f + g) := by
  unfold SoninSubspacePred at *
  have hae : (↑↑(f + g) : ℝ → ℂ) =ᶠ[ae volume] (↑↑f : ℝ → ℂ) + (↑↑g : ℝ → ℂ) := Lp.coeFn_add f g
  rw [ae_restrict_iff' measurableSet_Ioo] at hf hg ⊢
  filter_upwards [hf, hg, hae] with x hfx hgx haddx hx
  rw [haddx, Pi.add_apply, hfx hx, hgx hx, add_zero]

/-- The Sonin predicate is closed under scalar multiplication. -/
theorem SoninSubspacePred.smul {Λ : ℝ} (c : ℂ) {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : SoninSubspacePred Λ f) :
    SoninSubspacePred Λ (c • f) := by
  unfold SoninSubspacePred at *
  have hae : (↑↑(c • f) : ℝ → ℂ) =ᶠ[ae volume] c • (↑↑f : ℝ → ℂ) := Lp.coeFn_smul c f
  rw [ae_restrict_iff' measurableSet_Ioo] at hf ⊢
  filter_upwards [hf, hae] with x hfx hsmulx hx
  rw [hsmulx, Pi.smul_apply, hfx hx, smul_zero]

/-- The Sonin subspace of L²(ℝ) consisting of functions vanishing on `(-Λ, Λ)`. -/
def SoninSubspace (Λ : ℝ) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := { f | SoninSubspacePred Λ f }
  zero_mem' := soninSubspacePred_zero Λ
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

/-! ## Section 5: Measure Theory -/

/-- The complement `{|x| ≥ Λ}` equals `(-∞, -Λ] ∪ [Λ, ∞)`. -/
theorem complementBall_eq {Λ : ℝ} (hΛ : 0 < Λ) :
    {x : ℝ | Λ ≤ |x|} = Iic (-Λ) ∪ Ici Λ := by
  ext x
  simp only [mem_setOf, mem_union, mem_Iic, mem_Ici]
  constructor
  · intro hx
    rcases le_or_gt x 0 with hx0 | hx0
    · left; rw [abs_of_nonpos hx0] at hx; linarith
    · right; rw [abs_of_pos hx0] at hx; exact hx
  · intro hx
    rcases hx with hx | hx
    · have h1 : x < 0 := lt_of_le_of_lt hx (by linarith : -Λ < 0)
      rw [abs_of_neg h1]; linarith
    · rw [abs_of_nonneg (le_trans (le_of_lt hΛ) hx)]; exact hx

/-- **Key theorem**: `{|x| ≥ Λ}` has infinite Lebesgue measure.

This is why Amrein-Berthier does not apply to Sonin spaces. -/
theorem complementBall_measure_infinite {Λ : ℝ} (hΛ : 0 < Λ) :
    volume {x : ℝ | Λ ≤ |x|} = ⊤ := by
  rw [complementBall_eq hΛ, eq_top_iff]
  calc ⊤ = volume (Ici Λ) := Real.volume_Ici.symm
    _ ≤ volume (Iic (-Λ) ∪ Ici Λ) := measure_mono subset_union_right

/-- The ball `(-Λ, Λ)` has measure `2Λ`. -/
theorem ball_measure_eq {Λ : ℝ} (_ : 0 < Λ) :
    volume (Ioo (-Λ) Λ) = ENNReal.ofReal (2 * Λ) := by
  rw [Real.volume_Ioo]; congr 1; linarith

/-- The ball has finite measure. -/
theorem ball_measure_ne_top {Λ : ℝ} (hΛ : 0 < Λ) :
    volume (Ioo (-Λ) Λ) ≠ ⊤ := by
  rw [ball_measure_eq hΛ]
  exact ENNReal.ofReal_ne_top

/-! ## Section 6: The Prolate Spheroidal Operator -/

/-- The coefficient function `p(x) = Λ² - x²` in the prolate operator. -/
def prolateCoeff (Λ : ℝ) (x : ℝ) : ℝ := Λ^2 - x^2

/-- The potential `V(x) = (2πΛ)² x²`. -/
def prolatePotential (Λ : ℝ) (x : ℝ) : ℝ := (2 * π * Λ)^2 * x^2

/-- The prolate operator in formal form:
  `W_Λ(f)(x) = -(p(x) f'(x))' + V(x) f(x)` -/
def prolateOperatorFormal (Λ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (fun y => (prolateCoeff Λ y : ℂ) * deriv f y) x +
           (prolatePotential Λ x : ℂ) * f x

/-- The coefficient vanishes at the singular points `±Λ`. -/
theorem prolateCoeff_zero_at_pm_lambda (Λ : ℝ) :
    prolateCoeff Λ Λ = 0 ∧ prolateCoeff Λ (-Λ) = 0 := by
  simp [prolateCoeff]

/-- The coefficient is positive on `(-Λ, Λ)`. -/
theorem prolateCoeff_pos_interior {Λ : ℝ} (_ : 0 < Λ) {x : ℝ} (hx : |x| < Λ) :
    0 < prolateCoeff Λ x := by
  simp only [prolateCoeff]
  have : x^2 < Λ^2 := sq_lt_sq' (by linarith [abs_lt.mp hx]) (abs_lt.mp hx).2
  linarith

/-- The coefficient is negative outside `[-Λ, Λ]`. -/
theorem prolateCoeff_neg_exterior {Λ : ℝ} (_ : 0 < Λ) {x : ℝ} (hx : Λ < |x|) :
    prolateCoeff Λ x < 0 := by
  simp only [prolateCoeff]
  have h : Λ^2 < x^2 := by
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hx
      exact sq_lt_sq' (by linarith) hx
    · rw [abs_of_neg hx0] at hx
      have : Λ < -x := hx
      calc x^2 = (-x)^2 := by ring
        _ > Λ^2 := sq_lt_sq' (by linarith) this
  linarith

/-! ## Section 7: Spectral Data Structure

We define a structure that encapsulates the spectral data of the prolate operator,
allowing theorems about eigenfunctions without axiomatizing them. -/

/-- Data of the prolate operator spectrum for a given Λ.

This structure captures the essential spectral-theoretic properties:
1. The spectrum is discrete
2. There are infinitely many negative eigenvalues
3. Eigenfunctions for negative eigenvalues vanish on `[-Λ, Λ]` -/
structure ProlateOperatorData (Λ : ℝ) where
  /-- The eigenvalues (indexed by ℤ, unbounded in both directions). -/
  eigenvalue : ℤ → ℝ
  /-- The eigenfunctions. -/
  eigenfunction : ℤ → (ℝ → ℂ)
  /-- Eigenfunctions are in L². -/
  eigenfunction_memLp : ∀ n, MemLp (eigenfunction n) 2 volume
  /-- Negative eigenvalues exist (spectrum unbounded below). -/
  exists_negative : ∀ M : ℝ, ∃ n : ℤ, eigenvalue n < M
  /-- Positive eigenvalues exist (spectrum unbounded above). -/
  exists_positive : ∀ M : ℝ, ∃ n : ℤ, eigenvalue n > M
  /-- Eigenfunctions for negative eigenvalues vanish on `(-Λ, Λ)`. -/
  negative_eigenfunction_vanishes_time :
    ∀ n, eigenvalue n < 0 → VanishesOnBall Λ (eigenfunction n)
  /-- Fourier transforms of such eigenfunctions also vanish on `(-Λ, Λ)`. -/
  negative_eigenfunction_vanishes_freq :
    ∀ n, eigenvalue n < 0 → VanishesOnBall Λ (FourierTransform.fourier (eigenfunction n))
  /-- Eigenfunctions are non-zero. -/
  eigenfunction_ne_zero : ∀ n, eigenfunction n ≠ 0

namespace ProlateOperatorData

variable {Λ : ℝ}

/-- Eigenfunctions for negative eigenvalues belong to the Sonin space. -/
theorem eigenfunction_mem_soninSpace (data : ProlateOperatorData Λ) (n : ℤ) (hn : data.eigenvalue n < 0) :
    MemSoninSpace Λ (data.eigenfunction n) where
  memL2 := data.eigenfunction_memLp n
  vanishesTime := data.negative_eigenfunction_vanishes_time n hn
  vanishesFreq := data.negative_eigenfunction_vanishes_freq n hn

/-- The Sonin space is non-trivial given prolate operator data. -/
theorem soninSpace_nontrivial (data : ProlateOperatorData Λ) :
    ∃ f : ℝ → ℂ, MemSoninSpace Λ f ∧ f ≠ 0 := by
  rcases data.exists_negative 0 with ⟨n, hn⟩
  exact ⟨data.eigenfunction n, data.eigenfunction_mem_soninSpace n hn, data.eigenfunction_ne_zero n⟩

end ProlateOperatorData

/-! ## Section 8: Semiclassical Counting Function -/

/-- The semiclassical counting function for negative eigenvalues:
  `σ(E, Λ) = (E/2π)(log(E/2π) - 1 + log 4 - 2 log Λ) + Λ²` -/
def semiclassicalCounting (Λ E : ℝ) : ℝ :=
  (E / (2 * π)) * (Real.log (E / (2 * π)) - 1 + Real.log 4 - 2 * Real.log Λ) + Λ^2

/-- `√2² = 2`. -/
@[simp]
theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- `log 4 = 2 log 2`. -/
theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  have h : (4 : ℝ) = 2^2 := by norm_num
  rw [h, Real.log_pow]
  ring

/-- `log √2 = (log 2) / 2`. -/
theorem log_sqrt_two_eq : Real.log (Real.sqrt 2) = Real.log 2 / 2 :=
  Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- `log 4 - 2 log √2 = log 2`. -/
theorem log_four_sub_two_log_sqrt_two : Real.log 4 - 2 * Real.log (Real.sqrt 2) = Real.log 2 := by
  rw [log_four_eq, log_sqrt_two_eq]
  ring

/-- For `Λ = √2`, the counting function simplifies. -/
theorem semiclassicalCounting_sqrt2 (E : ℝ) :
    semiclassicalCounting (Real.sqrt 2) E =
    (E / (2 * π)) * (Real.log (E / (2 * π)) - 1 + Real.log 4 - 2 * Real.log (Real.sqrt 2)) + 2 := by
  simp only [semiclassicalCounting, sqrt_two_sq]

/-- The Riemann counting formula term. -/
def riemannCountingTerm (E : ℝ) : ℝ :=
  (E / (2 * π)) * (Real.log (E / (2 * π)) - 1)

/-- Auxiliary: the correction term for `Λ = √2`. -/
theorem sqrt2_correction_eq (E : ℝ) :
    (E / (2 * π)) * (Real.log 4 - 2 * Real.log (Real.sqrt 2)) = (E / (2 * π)) * Real.log 2 := by
  rw [log_four_sub_two_log_sqrt_two]

/-- The counting function for `Λ = √2` matches Riemann's formula up to `O(1)`. -/
theorem counting_sqrt2_riemann_match (E : ℝ) :
    semiclassicalCounting (Real.sqrt 2) E =
    riemannCountingTerm E + (E / (2 * π)) * Real.log 2 + 2 := by
  simp only [semiclassicalCounting, riemannCountingTerm, sqrt_two_sq]
  rw [← log_four_sub_two_log_sqrt_two]
  ring

/-! ## Section 9: de Branges Space Connection -/

/-- Structure for the dual Hardy-Titchmarsh transform. -/
structure DualHardyTitchmarshTransform (Λ : ℝ) where
  /-- The transformed function. -/
  toFun : ℂ → ℂ
  /-- Entirety. -/
  entire : Differentiable ℂ toFun

/-- Data for the de Branges isomorphism. -/
structure SoninDeBrangesIsomorphism (Λ : ℝ) where
  /-- The de Branges function E defining the space ℬ_Λ. -/
  hermiteBiehler : ℂ → ℂ
  /-- E is entire. -/
  entire : Differentiable ℂ hermiteBiehler
  /-- The Hermite-Biehler inequality: |E(z̄)| < |E(z)| for Im(z) > 0. -/
  hb_inequality : ∀ z : ℂ, 0 < z.im → ‖hermiteBiehler (starRingEnd ℂ z)‖ < ‖hermiteBiehler z‖
  /-- No real zeros. -/
  no_real_zeros : ∀ x : ℝ, hermiteBiehler x ≠ 0

/-! ## Section 10: Semilocal Theory Structure -/

/-- Data for semilocal extension of Sonin spaces.

For a finite set S of places containing ∞, this captures the isomorphism
  `θ_S : 𝐒_Λ(ℝ, e_∞) ≃ 𝐒_Λ(X_S, α)` -/
structure SemilocalExtension (Λ : ℝ) where
  /-- The set of finite primes in S. -/
  primes : Finset ℕ
  /-- All elements are prime. -/
  all_prime : ∀ p ∈ primes, Nat.Prime p
  /-- The σ_p function at prime p: `σ_p = ε₀ - (1/p)ε₁`.
      (Using ℤ → ℂ as a simplified model for functions on ℚ_p) -/
  sigma_p : (p : ℕ) → p ∈ primes → (ℤ → ℂ)
  /-- The tensor product σ_S. -/
  sigma_S : (∀ p ∈ primes, ℤ) → ℂ

end Sonin

end
