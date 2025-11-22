import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Real
namespace Gamma

/-- For a in [1/2, 1], Gamma(a) ≤ Gamma(1/2) = √π.
This uses convexity of Gamma and the fact that Γ(1) = 1 < √π = Γ(1/2). -/
lemma Gamma_le_Gamma_one_half {a : ℝ} (ha_low : 1/2 ≤ a) (ha_high : a ≤ 1) :
    Real.Gamma a ≤ Real.Gamma (1/2) := by
  -- Use that Γ is convex and Γ(1) < Γ(1/2)
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h_half : Real.Gamma (1/2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  -- √π > 1
  have h_sqrt_pi_gt_one : 1 < Real.sqrt Real.pi := by
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff (by aesop)]
    have : (1 : ℝ) < 3 := by norm_num
    exact this.trans Real.pi_gt_three
  -- Express a as convex combination: a = (2-2a)·(1/2) + (2a-1)·1
  let t := 2 - 2*a
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have ha_conv : a = t * (1/2) + (1-t) * 1 := by field_simp [t]; ring
  -- Apply convexity
  have := h_convex.2 (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1)
    ht_nonneg (by linarith : 0 ≤ 1-t) (by linarith : t + (1-t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc Real.Gamma a
      = Real.Gamma (t * (1/2) + (1-t) * 1) := by rw [ha_conv]
    _ ≤ t * Real.Gamma (1/2) + (1-t) * Real.Gamma 1 := this
    _ = t * Real.Gamma (1/2) + (1-t) * 1 := by rw [h1]
    _ ≤ t * Real.Gamma (1/2) + (1-t) * Real.Gamma (1/2) := by
        gcongr; rw [← h1]; rw [h1]; exact sub_nonneg_of_le ht_le_one; grind
    _ = Real.Gamma (1/2) := by ring

end Gamma
end Real
open Gamma Real

/-- For `a ∈ [1/2, 1]` we have `∫₁^∞ e^{-t} t^{a-1} ≤ √π`. -/
lemma integral_exp_neg_rpow_Ioi_one_le {a : ℝ}
    (ha_low : (1 / 2 : ℝ) ≤ a) (ha_high : a ≤ 1) :
    ∫ t in Ioi 1, Real.exp (-t) * t ^ (a - 1) ≤ Real.sqrt Real.pi := by
  /- Split the Γ-integral over `(0, ∞)` into `(0,1] ∪ (1,∞)`. -/
  have h_split :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) ∂volume) =
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) ∂volume) +
        (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1) ∂volume) := by
    -- first: integrability on the pieces
    have h_int_Ioc :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioc 0 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set Ioc_subset_Ioi_self
    have h_int_Ioi :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioi 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set (by
        intro x hx
        exact (lt_trans (by norm_num : (0 : ℝ) < 1) hx))
    -- now the additivity of the set integral
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi h_int_Ioc h_int_Ioi)
  /- The integral on `(0,1]` is non-negative. -/
  have h_nonneg :
      (0 : ℝ) ≤ ∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht.1) _)
  /- 1.  Throw away the non-negative part on `(0,1]`. -/
  have h_step₁ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := by
    simpa using
      (le_add_of_nonneg_right
          (a := ∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
          h_nonneg)
  /- 2.  Replace the whole right-hand side by the Γ-integral. -/
  have h_step₂ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) =
        ∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) := by
    simpa [add_comm] using h_split.symm
  /- 3.  Turn that into `Γ(a)`. -/
  have h_step₃ :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1)) = Real.Gamma a := by
    simpa using (Real.Gamma_eq_integral (by linarith : 0 < a)).symm
  /- 4.  Collect the inequalities. -/
  have h_le_Gamma :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma a := by
    have : (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := h_step₁
    simpa [h_step₂, h_step₃] using this
  /- 5.  Use the monotonicity of `Γ`. -/
  have :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ Real.Gamma (1 / 2) :=
    h_le_Gamma.trans (Gamma_le_Gamma_one_half ha_low ha_high)
  /- 6.  Finish with `Γ(1/2) = √π`. -/
  have hGammaHalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hGammaInv : Real.Gamma (2⁻¹) = Real.sqrt Real.pi := by
    simp_rw [inv_eq_one_div]
    aesop
  simpa [hGammaHalf, hGammaInv] using this

-- 1) A simp lemma for the real part of a negated complex number
@[simp] lemma Complex.re_neg_eq_neg_re (z : ℂ) : (-z).re = -z.re := by
  simp

-- 2) Interval-integrability of x^r on any [a,b] for volume when -1 < r
-- This is already in mathlib as intervalIntegral.intervalIntegrable_rpow'
-- Re-expose it (same name/signature) for convenience in this file.
theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ r) volume a b :=
  intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) h

-- Unit-interval power integral: ∫_{0}^{1} x^s dx = 1 / (s + 1), for s > -1
lemma intervalIntegral.integral_rpow_unit (s : ℝ) (hs : -1 < s) :
    ∫ x in (0 : ℝ)..1, x ^ s = 1 / (s + 1) := by
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hs))
  have hne : s + 1 ≠ 0 := by linarith
  simpa [one_rpow, zero_rpow hne] using h

lemma integral_rpow_Ioc_zero_one {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
  have h_eq : ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = ∫ t in (0)..(1), t ^ (s - 1) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  rw [h_eq]
  have hne : s - 1 ≠ -1 := by linarith
  have hlt : -1 < s - 1 := by linarith
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hlt))
  simp [one_rpow, zero_rpow hs.ne'] at h
  simp only [one_div, h]

namespace Complex.Gammaℝ

/- Bound on the norm of `Complex.Gamma` for points with real part in `[1/2, 1]`. -/

/-- A uniform bound on `‖Γ(w)‖` when `Re w ∈ [a,1] ⊆ [1/2,1]`. -/
lemma norm_Complex_Gamma_le_of_re_ge' {w : ℂ} {a : ℝ}
    (ha_low : (1/2 : ℝ) ≤ a) (_ : a ≤ 1)
    (hw     : a ≤ w.re)       (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  have hw_pos : 0 < w.re := by
    have : (0 : ℝ) < (1 / 2) := by norm_num
    exact this.trans_le (ha_low.trans hw)
  have ha_pos : 0 < a := (lt_of_lt_of_le (by norm_num) ha_low)

  have hΓ : Complex.Gamma w =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1) := by
    simpa [Complex.GammaIntegral] using (Complex.Gamma_eq_integral hw_pos)
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖ := by
    rw [hΓ]

  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-t) * t ^ (w - 1)‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm _

  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-t) * t ^ (w - 1)‖
        = ∫ t in Ioi (0 : ℝ),
            Real.exp (-t) * t ^ (w.re - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (w - 1)‖ = t ^ (w.re - 1) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)
    simp [Complex.norm_exp, hcpow]

  have h_split :
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (w.re - 1))
        = (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
        + (∫ t in Ioi 1,   Real.exp (-t) * t ^ (w.re - 1)) := by
    -- integrability on both parts
    have hIoc : IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (w.re - 1))
                              (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (w.re - 1))
                              (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one ht))
    -- use additivity of the set integral
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi hIoc hIoi)

  have h_ae :
      (fun t : ℝ ↦ Real.exp (-t) * t ^ (w.re - 1))
        ≤ᵐ[volume.restrict (Ioc 0 1)]
      (fun t : ℝ ↦                 t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro t
    intro ht
    -- here `ht : t ∈ Ioc 0 1`, i.e. `0 < t ∧ t ≤ 1`
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa using mul_le_of_le_one_left h_nonneg h_exp

  have hIoc₁ :
      IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (w.re - 1)) (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
   -- integrability of t ^ (w.re - 1) on (0,1]
  have hIoc₂ :
      IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    -- step 1 : interval–integrability on [0,1]
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 := by
      simpa using
        intervalIntegrable_rpow' (by linarith : -1 < w.re - 1) 0 1
    -- step 2 : turn that into an `IntegrableOn (Ioc 0 1)`
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (μ := volume) (a := 0) (b := 1) zero_le_one).1 hInt

  -- drop the exponential on (0,1]
  have h_drop_exp :
      (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) := setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae


  -- piece on (0,1]
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    integral_rpow_Ioc_zero_one hw_pos

  -- piece on (1, ∞)
  have h_Ioi_bound :
      ∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)
        ≤ Real.sqrt Real.pi := by
    have h_low : (1 / 2 : ℝ) ≤ w.re := ha_low.trans hw
    exact integral_exp_neg_rpow_Ioi_one_le h_low hw_ub

  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
          + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) := by
    -- chain of equalities/inequalities constructed above
    -- chain of equalities/inequalities constructed above
    have H :
        ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖
          ≤ (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
            + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) := by
      calc
        _ ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-t) * t ^ (w - 1)‖ := h_le_int
        _ = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (w.re - 1) := by
              simp_rw [h_int_real]
        _ = (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
              + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) := h_split
    have :
        ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖
          ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
            + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) :=
      H.trans (add_le_add_right h_drop_exp _)
    simpa [h_norm] using this

  -- now insert the explicit bounds found above
  have h_big' :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    have : (∫ t in Ioc 0 1, t ^ (w.re - 1))
            + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1))
          ≤ 1 / w.re + Real.sqrt Real.pi := by
      simpa [h_Ioc_exact]
        using h_Ioi_bound
    exact h_big.trans this

  have h_one_div : 1 / w.re ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    add_le_add_right h_one_div _
  exact h_big'.trans this

lemma setIntegral_mono_ae_restrict {α} [MeasurableSpace α] {μ : Measure α}
  {s : Set α} {f g : α → ℝ}
  (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
  (hfg : f ≤ᵐ[μ.restrict s] g) :
  ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  MeasureTheory.setIntegral_mono_ae_restrict hf hg hfg

/-- Bound on the norm of `Complex.Gamma` when `0 < a ≤ re w ≤ 1`. -/
lemma norm_Complex_Gamma_le_of_re_ge {w : ℂ} {a : ℝ}
    (ha_pos : 0 < a) (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  -- abbreviations that will be useful a lot
  set f : ℝ → ℂ := fun t ↦ Complex.exp (-t) * t ^ (w - 1)
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (w.re - 1)
  have hw_pos : 0 < w.re := ha_pos.trans_le hw

  -- 1.  Integral representation of Γ and the "norm ≤ integral‐of‐norm" trick
  have hΓ : Complex.Gamma w = ∫ t in Ioi (0 : ℝ), f t := by
    rw [Complex.Gamma_eq_integral hw_pos]
    simp [Complex.GammaIntegral, f]  -- Changed from rfl to simp
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), f t‖ := by
    simp [hΓ]
  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm _

  -- 2.  Turn the complex norm under the integral into a real function
  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖f t‖
        = ∫ t in Ioi (0 : ℝ), g t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    simp [f, g, Complex.norm_exp,
          Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)]

  have h_split :
      (∫ t in Ioi (0 : ℝ), g t)
        = (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
    -- integrability facts
    have hIoc : IntegrableOn g (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn g (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))  -- Fixed
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := 0) (b := 1))
          measurableSet_Ioi hIoc hIoi)

  -- 4.  On (0,1] we drop the exponential
  have h_ae_drop :
      (fun t : ℝ ↦ g t)
        ≤ᵐ[volume.restrict (Ioc 0 1)]
      (fun t : ℝ ↦ t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall ?_)
    intro t ht
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa [g] using mul_le_of_le_one_left h_nonneg h_exp

  -- integrability on (0,1] of both functions
  have hIoc₁ : IntegrableOn g (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
  have hIoc₂ : IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    -- intervalIntegrable on `[0,1]`
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 := by
      simpa using
        intervalIntegrable_rpow' (by linarith : -1 < w.re - 1) 0 1
    -- turn it into `IntegrableOn`
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (a := 0) (b := 1) zero_le_one).1 hInt

  have h_drop_exp :
      (∫ t in Ioc 0 1, g t)
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) :=
    setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae_drop

  -- 5.  Collect steps 1–4  →  `‖Γ(w)‖ ≤ A' + B`
  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
          + (∫ t in Ioi 1, g t) := by
    have step1 : ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
      simpa [h_int_real, h_split] using h_le_int
    -- now replace the first summand by the smaller integral without `exp`
    have step2 : (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t)
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
          + (∫ t in Ioi 1, g t) := by
      exact add_le_add_right h_drop_exp _
    simpa [h_norm] using (le_trans step1 step2)

  -- 6.  Evaluate explicitly the integral on (0,1]
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    integral_rpow_Ioc_zero_one hw_pos

  -- 7.  Bound the tail integral ∫₁^∞ …  by √π
  have h_tail :
      ∫ t in Ioi 1, g t ≤ Real.sqrt Real.pi := by
    -- split the two cases w.re ≥ 1/2  and  w.re < 1/2
    by_cases hhalf : (1/2 : ℝ) ≤ w.re
    · -- we can apply the lemma proved earlier
      have := integral_exp_neg_rpow_Ioi_one_le hhalf hw_ub
      simpa [g] using this
    · -- compare to the 1/2–exponent
      have h_ae :
          (fun t : ℝ ↦ g t)
            ≤ᵐ[volume.restrict (Ioi 1)]
          (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1/2 : ℝ) - 1)) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall ?_)
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hpow : t ^ (w.re - 1) ≤ t ^ ((1/2 : ℝ) - 1) := by
          have : w.re - 1 ≤ (1/2 : ℝ) - 1 := by linarith [hhalf]
          exact Real.rpow_le_rpow_of_exponent_le ht1 this
        have hnonneg : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
        simpa [g] using mul_le_mul_of_nonneg_left hpow hnonneg
      -- integrability of both functions on (1,∞)
      have hIntL : IntegrableOn g (Ioi 1) :=
        (Real.GammaIntegral_convergent hw_pos).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))  -- Fixed
      have hIntR : IntegrableOn
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1/2 : ℝ) - 1)) (Ioi 1) :=
        (Real.GammaIntegral_convergent (by norm_num : 0 < (1/2 : ℝ))).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))  -- Fixed
      have h_le : ∫ t in Ioi 1, g t
            ≤ ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1/2 : ℝ) - 1) :=
        setIntegral_mono_ae_restrict hIntL hIntR h_ae
      -- and that last integral is ≤ √π
      have h_upper :
          ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1/2 : ℝ) - 1)
            ≤ Real.sqrt Real.pi := by
        have := integral_exp_neg_rpow_Ioi_one_le
                  (by norm_num : (1/2 : ℝ) ≤ 1/2)
                  (by norm_num : (1/2 : ℝ) ≤ (1 : ℝ))
        simpa using this
      exact h_le.trans h_upper

  -- 8.  Put everything together
  have h_main :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    calc ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := h_big
      _ = 1 / w.re + (∫ t in Ioi 1, g t) := by rw [h_Ioc_exact]
      _ ≤ 1 / w.re + Real.sqrt Real.pi := by
          exact add_le_add_left h_tail _

  -- 9.  replace 1 / w.re by the slightly larger 1 / a
  have h_one_div : (1 / w.re : ℝ) ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    add_le_add_right h_one_div _
  exact h_main.trans this

end Complex.Gammaℝ
