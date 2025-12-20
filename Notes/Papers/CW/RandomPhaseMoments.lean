import Notes.Papers.CW.ZetaSpinGlassDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped BigOperators Interval

namespace ZetaSpinGlass

/-!
## Random phase moments (uniform on `[0,2π]`)

This file isolates the basic harmonic-analysis facts used throughout CW/Arguin/Burnol:
expectations of trigonometric polynomials under the uniform measure on `[0,2π]`.

These are the input lemmas for:
- centering (`𝔼[cos(θ-a)] = 0`, `𝔼[cos(2(θ-a))] = 0`),
- covariance computations (`𝔼[cos(θ-a)cos(θ-b)] = (1/2)cos(a-b)`),
- and hence explicit covariance kernels for random prime-phase blocks.

We work with the *explicit* probability measure
`μθ := (volume (Icc 0 (2π)))⁻¹ • volume.restrict (Icc 0 (2π))`
to avoid typeclass diamonds and keep the result stable under refactors.
-/

section Uniform

/-- The explicit uniform probability measure on `[0,2π]`. -/
noncomputable def uniformIcc0TwoPi : Measure ℝ :=
  (volume (Set.Icc (0 : ℝ) (2 * Real.pi)))⁻¹ •
    (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))

def I : Set ℝ := Set.Icc (0 : ℝ) (2 * Real.pi)

lemma uniformIcc0TwoPi_isProbabilityMeasure :
    IsProbabilityMeasure (uniformIcc0TwoPi) := by
  classical
  refine ⟨?_⟩
  -- `μ(univ) = vol(I)⁻¹ * vol(I) = 1`, with `I = Icc 0 (2π)`.
  have hvol_ne_zero : volume I ≠ (0 : ENNReal) := by
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    have : (ENNReal.ofReal (2 * Real.pi)) ≠ (0 : ENNReal) := by
      have : ¬ (2 * Real.pi) ≤ 0 := not_le.mpr hpos
      simpa [ENNReal.ofReal_eq_zero] using this
    simpa [I, Real.volume_Icc] using this
  have hvol_ne_top : volume I ≠ (⊤ : ENNReal) := by
    have : (ENNReal.ofReal (2 * Real.pi)) ≠ (⊤ : ENNReal) := by
      simpa using (ENNReal.ofReal_ne_top (r := (2 * Real.pi)))
    simpa [I, Real.volume_Icc] using this
  have hmass : uniformIcc0TwoPi Set.univ = (volume I)⁻¹ * (volume I) := by
    simp [uniformIcc0TwoPi, I, Measure.smul_apply, Measure.restrict_apply, MeasurableSet.univ,
      Set.univ_inter]
  simp [hmass, ENNReal.inv_mul_cancel hvol_ne_zero hvol_ne_top]

lemma integral_restrict_I_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ x, f x ∂ (volume.restrict I)) = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc
    (∫ x, f x ∂ (volume.restrict I))
        = (∫ x in I, f x ∂ (volume : Measure ℝ)) := by rfl
    _ = (∫ x in Set.Ioc (0 : ℝ) (2 * Real.pi), f x ∂ (volume : Measure ℝ)) := by
          simpa [I] using
            (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ)) (f := f)
              (x := (0 : ℝ)) (y := (2 * Real.pi)))
    _ = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
          simpa using
            (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) (f := f) hab).symm

lemma intervalIntegral_cos_sub_eq_zero (a : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (x - a)) = 0 := by
  have hshift :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (x - a))
        = ∫ x : ℝ in (0 : ℝ) + (-a)..(2 * Real.pi) + (-a), Real.cos x := by
    -- shift by `-a`
    simp [sub_eq_add_neg]
  rw [hshift]
  have hsin : Real.sin (2 * Real.pi + -a) = Real.sin (-a) := by
    simp [add_comm]
  simp [hsin]

lemma integral_cos_sub (a : ℝ) :
    (∫ x, Real.cos (x - a) ∂ uniformIcc0TwoPi) = 0 := by
  classical
  have hscale :
      (∫ x, Real.cos (x - a) ∂ uniformIcc0TwoPi)
        = ((volume I)⁻¹).toReal * (∫ x, Real.cos (x - a) ∂ (volume.restrict I)) := by
    simp [uniformIcc0TwoPi, I, smul_eq_mul]
  rw [hscale]
  rw [integral_restrict_I_eq_intervalIntegral (f := fun x => Real.cos (x - a))]
  simp [intervalIntegral_cos_sub_eq_zero (a := a)]

lemma intervalIntegral_cos_two_mul_sub_eq_zero (a : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * (x - a))) = 0 := by
  classical
  -- rewrite integrand as `cos (2*x + (-2*a))`, then use the affine change of variables
  have hEq :
      Set.EqOn (fun x : ℝ => Real.cos (2 * (x - a))) (fun x => Real.cos (2 * x + (-2 * a)))
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    intro x hx
    have : 2 * (x - a) = 2 * x + (-2 * a) := by ring
    simp [this]
  have hcongr :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * (x - a)))
        = ∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * x + (-2 * a)) :=
    intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi)) hEq
  rw [hcongr]
  have hcomp :=
    (intervalIntegral.integral_comp_mul_add (f := fun x : ℝ => Real.cos x)
      (a := (0 : ℝ)) (b := (2 * Real.pi)) (c := (2 : ℝ)) (d := (-2 * a))
      (hc := (by norm_num : (2 : ℝ) ≠ 0)))
  rw [hcomp]
  have hsin : Real.sin (2 * (2 * Real.pi) + (-2 * a)) = Real.sin (-2 * a) := by
    have hper : Real.sin ((-2 * a) + (2 : ℕ) * (2 * Real.pi)) = Real.sin (-2 * a) :=
      Real.sin_add_nat_mul_two_pi (-2 * a) 2
    have hcomm : (-2 * a) + (2 : ℝ) * (2 * Real.pi) = 2 * (2 * Real.pi) + (-2 * a) := by ring
    simpa [hcomm, two_mul, add_assoc, add_left_comm, add_comm] using hper
  have hneg : 2 * (2 * Real.pi) + (-(2 * a)) = 2 * (2 * Real.pi) + (-2 * a) := by ring
  simp [hneg, hsin]

/-!
### Higher-frequency cosine integrals

For covariance computations we also need `∫₀^{2π} cos(n (x-a)) = 0` for any natural frequency
`n ≠ 0`. We package this once; the `n = 1,2` lemmas above are convenient special cases.
-/

lemma intervalIntegral_cos_nat_mul_sub_eq_zero (n : ℕ) (hn : n ≠ 0) (a : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos ((n : ℝ) * (x - a))) = 0 := by
  -- rewrite to affine form `cos ((n:ℝ) * x + d)` on `[0,2π]`
  have hEq :
      Set.EqOn (fun x : ℝ => Real.cos ((n : ℝ) * (x - a)))
        (fun x => Real.cos ((n : ℝ) * x + (-(n : ℝ) * a)))
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    intro x hx
    have : (n : ℝ) * (x - a) = (n : ℝ) * x + (-(n : ℝ) * a) := by ring
    simp [this]
  have hcongr :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos ((n : ℝ) * (x - a)))
        =
        ∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos ((n : ℝ) * x + (-(n : ℝ) * a)) :=
    intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi)) hEq
  rw [hcongr]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hcomp :=
    (intervalIntegral.integral_comp_mul_add (f := fun x : ℝ => Real.cos x)
      (a := (0 : ℝ)) (b := (2 * Real.pi)) (c := (n : ℝ)) (d := (-(n : ℝ) * a)) (hc := hn'))
  rw [hcomp]
  -- show the inner integral of `cos` vanishes by periodicity of `sin`
  have hI :
      (∫ x : ℝ in ((n : ℝ) * (0 : ℝ) + (-(n : ℝ) * a))..((n : ℝ) * (2 * Real.pi) + (-(n : ℝ) * a)),
          Real.cos x) = 0 := by
    rw [integral_cos]
    have hsin :
        Real.sin ((n : ℝ) * (2 * Real.pi) + (-(n : ℝ) * a))
          = Real.sin ((n : ℝ) * (0 : ℝ) + (-(n : ℝ) * a)) := by
      have h0 : (n : ℝ) * (0 : ℝ) + (-(n : ℝ) * a) = -((n : ℝ) * a) := by ring
      have hper : Real.sin (-((n : ℝ) * a) + n * (2 * Real.pi)) = Real.sin (-((n : ℝ) * a)) :=
        Real.sin_add_nat_mul_two_pi (-((n : ℝ) * a)) n
      have htop : (n : ℝ) * (2 * Real.pi) + (-(n : ℝ) * a) = -((n : ℝ) * a) + n * (2 * Real.pi) := by ring
      simp [add_comm]
    linarith
  -- avoid rewriting into `smul_eq_zero`; just rewrite the inner integral to `0`
  rw [hI]
  simp

lemma integral_cos_two_mul_sub (a : ℝ) :
    (∫ x, Real.cos (2 * (x - a)) ∂ uniformIcc0TwoPi) = 0 := by
  classical
  have hscale :
      (∫ x, Real.cos (2 * (x - a)) ∂ uniformIcc0TwoPi)
        = ((volume I)⁻¹).toReal * (∫ x, Real.cos (2 * (x - a)) ∂ (volume.restrict I)) := by
    simp [uniformIcc0TwoPi, I, smul_eq_mul]
  rw [hscale]
  rw [integral_restrict_I_eq_intervalIntegral (f := fun x => Real.cos (2 * (x - a)))]
  simp [intervalIntegral_cos_two_mul_sub_eq_zero (a := a)]

/-- Product-to-sum identity, specialized to cosine. -/
lemma cos_mul_cos (u v : ℝ) :
    Real.cos u * Real.cos v = (Real.cos (u - v) + Real.cos (u + v)) / 2 := by
  have h1 : Real.cos (u - v) = Real.cos u * Real.cos v + Real.sin u * Real.sin v := by
    simpa using (Real.cos_sub u v)
  have h2 : Real.cos (u + v) = Real.cos u * Real.cos v - Real.sin u * Real.sin v := by
    simpa using (Real.cos_add u v)
  have hsum : Real.cos (u - v) + Real.cos (u + v) = 2 * (Real.cos u * Real.cos v) := by
    calc
      Real.cos (u - v) + Real.cos (u + v)
          = (Real.cos u * Real.cos v + Real.sin u * Real.sin v)
              + (Real.cos u * Real.cos v - Real.sin u * Real.sin v) := by
                simp [h1, h2]
      _ = 2 * (Real.cos u * Real.cos v) := by ring
  nlinarith [hsum]

lemma intervalIntegral_cos_sub_mul_cos_two_mul_sub_eq_zero (a b : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (x - a) * Real.cos (2 * (x - b))) = 0 := by
  -- product-to-sum, then each cosine integral vanishes (frequencies 1 and 3)
  have hpoint : Set.EqOn
      (fun x : ℝ => Real.cos (x - a) * Real.cos (2 * (x - b)))
      (fun x : ℝ =>
          (Real.cos (2 * b - a - x) + Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3)))) / 2)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    intro x hx
    have h := cos_mul_cos (u := x - a) (v := 2 * (x - b))
    have huv : (x - a) - (2 * (x - b)) = -(x - (2 * b - a)) := by ring
    have huvp : (x - a) + (2 * (x - b)) = (3 : ℝ) * (x - ((a + 2 * b) / 3)) := by ring
    -- `cos` is even, so the first term simplifies
    simpa [huv, huvp, Real.cos_neg] using h
  rw [intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi)) hpoint]
  have hint1 :
      IntervalIntegrable (fun x : ℝ => Real.cos (2 * b - a - x)) (volume : Measure ℝ) (0 : ℝ) (2 * Real.pi) := by
    have : Continuous (fun x : ℝ => Real.cos (2 * b - a - x)) := by fun_prop
    exact this.intervalIntegrable _ _
  have hint2 :
      IntervalIntegrable (fun x : ℝ => Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3))))
        (volume : Measure ℝ) (0 : ℝ) (2 * Real.pi) := by
    have : Continuous (fun x : ℝ => Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3)))) := by fun_prop
    exact this.intervalIntegrable _ _
  have h1 :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * b - a - x)) = 0 := by
    -- rewrite by evenness to a standard shift integral
    have hEq' : Set.EqOn (fun x : ℝ => Real.cos (2 * b - a - x))
        (fun x : ℝ => Real.cos (x - (2 * b - a))) (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
      intro x hx
      have : 2 * b - a - x = -(x - (2 * b - a)) := by ring
      calc
        Real.cos (2 * b - a - x) = Real.cos (-(x - (2 * b - a))) := by
          rw [this]
        _ = Real.cos (x - (2 * b - a)) := by simpa using (Real.cos_neg (x - (2 * b - a)))
    have hcongr' :
        (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * b - a - x))
          = ∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (x - (2 * b - a)) :=
      intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi)) hEq'
    rw [hcongr']
    simpa using intervalIntegral_cos_sub_eq_zero (a := (2 * b - a))
  have h2 :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3)))) = 0 := by
    simpa using
      (intervalIntegral_cos_nat_mul_sub_eq_zero (n := 3) (hn := by decide) (a := ((a + 2 * b) / 3)))
  calc
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
        (Real.cos (2 * b - a - x) + Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3)))) / 2)
        = (1 / 2 : ℝ) *
            (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
              (Real.cos (2 * b - a - x) + Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3))))) := by
          simp [div_eq_mul_inv, mul_comm]
    _ = (1 / 2 : ℝ) *
          ((∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * b - a - x))
            + (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos ((3 : ℝ) * (x - ((a + 2 * b) / 3))))) := by
          have :=
            intervalIntegral.integral_add (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi))
              hint1 hint2
          simpa using this
    _ = 0 := by simp [h1, h2]

lemma integral_cos_sub_mul_cos_two_mul_sub_eq_zero (a b : ℝ) :
    (∫ x, Real.cos (x - a) * Real.cos (2 * (x - b)) ∂ uniformIcc0TwoPi) = 0 := by
  classical
  have hscale :
      (∫ x, Real.cos (x - a) * Real.cos (2 * (x - b)) ∂ uniformIcc0TwoPi)
        = ((volume I)⁻¹).toReal *
            (∫ x, Real.cos (x - a) * Real.cos (2 * (x - b)) ∂ (volume.restrict I)) := by
    simp [uniformIcc0TwoPi, I, smul_eq_mul]
  rw [hscale]
  rw [integral_restrict_I_eq_intervalIntegral
    (f := fun x => Real.cos (x - a) * Real.cos (2 * (x - b)))]
  simp [intervalIntegral_cos_sub_mul_cos_two_mul_sub_eq_zero (a := a) (b := b)]

lemma intervalIntegral_cos_two_mul_sub_mul_cos_two_mul_sub (a b : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * (x - a)) * Real.cos (2 * (x - b)))
      = Real.pi * Real.cos (2 * (b - a)) := by
  -- product-to-sum, then the oscillatory `4*` term integrates to zero
  have hpoint : Set.EqOn
      (fun x : ℝ => Real.cos (2 * (x - a)) * Real.cos (2 * (x - b)))
      (fun x : ℝ => (Real.cos (2 * (b - a)) + Real.cos (4 * (x - ((a + b) / 2)))) / 2)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    intro x hx
    have h := cos_mul_cos (u := 2 * (x - a)) (v := 2 * (x - b))
    have huv : (2 * (x - a)) - (2 * (x - b)) = 2 * (b - a) := by ring
    have huvp : (2 * (x - a)) + (2 * (x - b)) = 4 * (x - ((a + b) / 2)) := by ring
    simpa [huv, huvp] using h
  rw [intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi)) hpoint]
  have hInt_cos4 :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (4 * (x - ((a + b) / 2)))) = 0 := by
    -- frequency `4`
    simpa using
      (intervalIntegral_cos_nat_mul_sub_eq_zero (n := 4) (hn := by decide) (a := ((a + b) / 2)))
  have hint1 :
      IntervalIntegrable (fun _x : ℝ => (Real.cos (2 * (b - a)) : ℝ)) (volume : Measure ℝ) (0 : ℝ) (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hint2 :
      IntervalIntegrable (fun x : ℝ => Real.cos (4 * (x - ((a + b) / 2))))
        (volume : Measure ℝ) (0 : ℝ) (2 * Real.pi) := by
    have : Continuous (fun x : ℝ => Real.cos (4 * (x - ((a + b) / 2)))) := by fun_prop
    exact this.intervalIntegrable _ _
  calc
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
        (Real.cos (2 * (b - a)) + Real.cos (4 * (x - ((a + b) / 2)))) / 2)
        = (1 / 2 : ℝ) *
            (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
              (Real.cos (2 * (b - a)) + Real.cos (4 * (x - ((a + b) / 2))))) := by
          simp [div_eq_mul_inv, mul_comm]
    _ = (1 / 2 : ℝ) *
          ((∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), (Real.cos (2 * (b - a)) : ℝ))
            + (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (4 * (x - ((a + b) / 2))))) := by
          have :=
            intervalIntegral.integral_add (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi))
              hint1 hint2
          simpa using this
    _ = (1 / 2 : ℝ) * ((2 * Real.pi) * Real.cos (2 * (b - a)) + 0) := by
          simp [hInt_cos4]
    _ = Real.pi * Real.cos (2 * (b - a)) := by
          ring

lemma integral_cos_two_mul_sub_mul_cos_two_mul_sub (a b : ℝ) :
    (∫ x, Real.cos (2 * (x - a)) * Real.cos (2 * (x - b)) ∂ uniformIcc0TwoPi)
      = (1 / 2 : ℝ) * Real.cos (2 * (b - a)) := by
  classical
  have hscale :
      (∫ x, Real.cos (2 * (x - a)) * Real.cos (2 * (x - b)) ∂ uniformIcc0TwoPi)
        = ((volume I)⁻¹).toReal *
            (∫ x, Real.cos (2 * (x - a)) * Real.cos (2 * (x - b)) ∂ (volume.restrict I)) := by
    simp [uniformIcc0TwoPi, I, smul_eq_mul]
  rw [hscale]
  rw [integral_restrict_I_eq_intervalIntegral
    (f := fun x => Real.cos (2 * (x - a)) * Real.cos (2 * (x - b)))]
  rw [intervalIntegral_cos_two_mul_sub_mul_cos_two_mul_sub (a := a) (b := b)]
  have htoReal : ((volume I)⁻¹).toReal = (2 * Real.pi)⁻¹ := by
    have hpi : 0 ≤ (Real.pi : ℝ) := by positivity
    simp [I, Real.volume_Icc, ENNReal.toReal_inv, hpi]
  have : (2 * Real.pi)⁻¹ * (Real.pi * Real.cos (2 * (b - a))) =
      (1 / 2 : ℝ) * Real.cos (2 * (b - a)) := by
    field_simp [Real.pi_ne_zero]
  simp [htoReal, mul_assoc, mul_left_comm, mul_comm]

lemma intervalIntegral_cos_sub_mul_cos_sub (a b : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (x - a) * Real.cos (x - b))
      = Real.pi * Real.cos (b - a) := by
  -- rewrite integrand using product-to-sum
  have hpoint : Set.EqOn
      (fun x : ℝ => Real.cos (x - a) * Real.cos (x - b))
      (fun x : ℝ => (Real.cos (b - a) + Real.cos (2 * (x - ((a + b) / 2)))) / 2)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    intro x hx
    have h := cos_mul_cos (u := x - a) (v := x - b)
    have huv : (x - a) - (x - b) = b - a := by ring
    have huvp : (x - a) + (x - b) = 2 * (x - ((a + b) / 2)) := by ring
    simpa [huv, huvp] using h
  rw [intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi)) hpoint]
  have hInt_cos2 :
      (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * (x - ((a + b) / 2)))) = 0 :=
    intervalIntegral_cos_two_mul_sub_eq_zero (a := ((a + b) / 2))
  have hint1 :
      IntervalIntegrable (fun _x : ℝ => (Real.cos (b - a) : ℝ)) (volume : Measure ℝ) (0 : ℝ) (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hint2 :
      IntervalIntegrable (fun x : ℝ => Real.cos (2 * (x - ((a + b) / 2))))
        (volume : Measure ℝ) (0 : ℝ) (2 * Real.pi) := by
    have : Continuous (fun x : ℝ => Real.cos (2 * (x - ((a + b) / 2)))) := by
      fun_prop
    exact this.intervalIntegrable _ _
  calc
    (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
        (Real.cos (b - a) + Real.cos (2 * (x - ((a + b) / 2)))) / 2)
        = (1 / 2 : ℝ) *
            (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
              (Real.cos (b - a) + Real.cos (2 * (x - ((a + b) / 2))))) := by
          simp [div_eq_mul_inv, mul_comm]
    _ = (1 / 2 : ℝ) *
          ((∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), (Real.cos (b - a) : ℝ))
            + (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos (2 * (x - ((a + b) / 2))))) := by
          have :=
            intervalIntegral.integral_add (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (2 * Real.pi))
              hint1 hint2
          simpa using this
    _ = (1 / 2 : ℝ) * ((2 * Real.pi) * Real.cos (b - a) + 0) := by
          simp [hInt_cos2]
    _ = Real.pi * Real.cos (b - a) := by
          ring

lemma integral_cos_sub_mul_cos_sub (a b : ℝ) :
    (∫ x, Real.cos (x - a) * Real.cos (x - b) ∂ uniformIcc0TwoPi)
      = (1 / 2 : ℝ) * Real.cos (b - a) := by
  classical
  have hscale :
      (∫ x, Real.cos (x - a) * Real.cos (x - b) ∂ uniformIcc0TwoPi)
        = ((volume I)⁻¹).toReal *
            (∫ x, Real.cos (x - a) * Real.cos (x - b) ∂ (volume.restrict I)) := by
    simp [uniformIcc0TwoPi, I, smul_eq_mul]
  rw [hscale]
  rw [integral_restrict_I_eq_intervalIntegral (f := fun x => Real.cos (x - a) * Real.cos (x - b))]
  rw [intervalIntegral_cos_sub_mul_cos_sub (a := a) (b := b)]
  have htoReal : ((volume I)⁻¹).toReal = (2 * Real.pi)⁻¹ := by
    have hpi : 0 ≤ (Real.pi : ℝ) := by positivity
    simp [I, Real.volume_Icc, ENNReal.toReal_inv, hpi]
  -- `(2π)⁻¹ * (π * c) = (1/2) * c`
  -- (and we keep the cosine factor unchanged).
  -- `field_simp` clears denominators safely.
  have : (2 * Real.pi)⁻¹ * (Real.pi * Real.cos (b - a)) = (1 / 2 : ℝ) * Real.cos (b - a) := by
    field_simp [Real.pi_ne_zero]
  simp [htoReal, mul_assoc, mul_left_comm, mul_comm]

end Uniform

end ZetaSpinGlass
