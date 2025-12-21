import Riemann.PhysLean.SpinGlass.ComplexIBP
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Arguin–Tai (2018): the test function `F_p`

This file starts the formalization of the function `F_p(z, z̄)` from Arguin–Tai (2018),
used to apply the approximate complex IBP lemma (`SpinGlass.approx_integral_by_parts_complex`).

In the paper, for a fixed prime `p`, one defines (schematically)

`F_p(z, z̄) = (∫ ω_p(h) * exp(β(ω_p(h) z + \bar ω_p(h) \bar z) + Y_p(h)) dh)
             / (∫ exp(β(ω_p(h) z + \bar ω_p(h) \bar z) + Y_p(h)) dh)`.

We implement the same object as a genuine function `ℂ → ℂ`, interpreting `z̄ = conj z`.

The next step (in this file) will be to prove that `F_p` satisfies `FDerivLipschitz` with a
constant `M = O(p^{-3/2})` (uniformly in `z`), matching the heuristic bound in the paper.
-/

open scoped Real Topology BigOperators ComplexConjugate
open MeasureTheory Set Filter Complex

namespace SpinGlass

noncomputable section

/-! ## The base measure on `[0,1]` -/

def I01 : Set ℝ := Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to `[0,1]`. This is a probability measure since `vol(I01)=1`. -/
noncomputable def μ01 : Measure ℝ :=
  (volume.restrict I01)

lemma μ01_isProbabilityMeasure : IsProbabilityMeasure (μ01) := by
  classical
  refine ⟨?_⟩
  -- `μ01 univ = volume (I01) = 1`
  simp [μ01, I01, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]

instance : IsProbabilityMeasure μ01 := μ01_isProbabilityMeasure

instance : IsFiniteMeasure μ01 := by
  -- Reduce to the known instance for `volume.restrict (Icc 0 1)`.
  dsimp [μ01, I01]
  infer_instance

instance : NeZero μ01 := by
  refine ⟨?_⟩
  intro h0
  have hmass : μ01 Set.univ = (1 : ENNReal) := by
    -- `μ01 univ = volume (Icc 0 1) = 1`
    simp [μ01, I01, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  have hmass0 : μ01 Set.univ = 0 := by
    simpa [h0] using (show (0 : Measure ℝ) Set.univ = 0 by simp)
  simpa [hmass] using hmass0

/-! ## The coefficient `ω_p(h)` -/

/--
The paper’s coefficient
`ω_p(h) = (2 * √p)⁻¹ * p^{-i h} = (2 * √p)⁻¹ * exp(-i h log p)`.
-/
noncomputable def omega_p (p : ℕ) (h : ℝ) : ℂ :=
  (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) *
    Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))

lemma omega_p_norm (p : ℕ) (h : ℝ) :
    ‖omega_p p h‖ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
  -- `‖exp z‖ = exp (re z)` and the exponent is purely imaginary, hence has real part `0`.
  have hexp :
      ‖Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))‖ = 1 := by
    have hre : ((-Complex.I) * (h : ℂ) * (Real.log (p : ℝ) : ℂ)).re = 0 := by
      -- Avoid rewriting `Real.log n` to `Complex.log n` (it introduces irrelevant side-goals).
      simp [-Complex.natCast_log, -Complex.ofNat_log]
    simp [Complex.norm_exp, -Complex.natCast_log, -Complex.ofNat_log]
  have hsc : 0 ≤ (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by positivity
  have hnsc :
      ‖((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) : ℂ)‖ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
    -- `‖(r:ℂ)‖ = r` for `r ≥ 0`
    simp
  -- Pull out the real scalar and use `‖exp(...)‖ = 1`.
  calc
    ‖omega_p p h‖
        = ‖((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) : ℂ)‖
            * ‖Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))‖ := by
              -- Avoid rewriting `Real.log n` to `Complex.log n` (it breaks later rewrites),
              -- and avoid normal forms like `|√p|⁻¹ * 2⁻¹`.
              simp [omega_p, mul_assoc, -Complex.natCast_log, -Complex.ofNat_log]
    _ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
          -- avoid `simp` normal-form rewriting; just use our named equalities
          calc
            ‖((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) : ℂ)‖
                * ‖Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))‖
                = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * 1 := by
                    rw [hnsc, hexp]
            _ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by ring

lemma omega_p_norm_le (p : ℕ) (h : ℝ) :
    ‖omega_p p h‖ ≤ (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
  simp [omega_p_norm]

lemma measurable_omega_p (p : ℕ) : Measurable (omega_p p) := by
  unfold omega_p
  fun_prop

/-! ## The Arguin–Tai weight and the function `F_p` -/

/--
The real weight in the Gibbs-like average:

`w(z,h) = exp( 2*β*Re(omega_p(h) * z) + Y(h) )`.

This matches `exp(β(ω z + conj ω conj z) + Y)` since `ω z + conj ω conj z = 2 Re(ω z)`.
-/
noncomputable def arguinTaiWeight (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) (h : ℝ) : ℝ :=
  Real.exp (2 * β * ((omega_p p h * z).re) + Y h)

lemma arguinTaiWeight_pos (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) (h : ℝ) :
    0 < arguinTaiWeight β p Y z h := by
  simp [arguinTaiWeight, Real.exp_pos]

lemma measurable_arguinTaiWeight (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y) (z : ℂ) :
    Measurable (fun h => arguinTaiWeight β p Y z h) := by
  have hω : Measurable (omega_p p) := measurable_omega_p p
  have hre : Measurable (fun h => (omega_p p h * z).re) := by
    simpa using (Complex.continuous_re.measurable.comp (hω.mul measurable_const))
  have hlin : Measurable (fun h => (2 * β) * (omega_p p h * z).re + Y h) :=
    (measurable_const.mul hre).add hY
  simpa [arguinTaiWeight] using (Real.continuous_exp.measurable.comp hlin)

lemma integrable_arguinTaiWeight_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    Integrable (fun h => arguinTaiWeight β p Y z h) μ01 := by
  -- `μ01` is a finite measure, so bounded functions are integrable.
  have hmeas :
      AEStronglyMeasurable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)).aestronglyMeasurable
  -- crude uniform bound: `exp(2|β| * ‖ω‖ * ‖z‖ + CY)`
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  have hbound :
      ∀ᵐ h ∂μ01, ‖arguinTaiWeight β p Y z h‖ ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
    refine ae_of_all _ (fun h => ?_)
    have hω : ‖omega_p p h‖ ≤ Cω := by
      simpa [Cω] using omega_p_norm_le p h
    have hlin :
        2 * β * (omega_p p h * z).re + Y h
          ≤ 2 * |β| * Cω * ‖z‖ + CY := by
      have h1 :
          2 * β * (omega_p p h * z).re ≤ |2 * β * (omega_p p h * z).re| :=
        le_abs_self _
      have h2 :
          |2 * β * (omega_p p h * z).re|
            = 2 * |β| * |(omega_p p h * z).re| := by
        -- pull absolute values through scalar products
        simp [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)), mul_assoc, mul_left_comm, mul_comm]
      have h3 : |(omega_p p h * z).re| ≤ ‖omega_p p h‖ * ‖z‖ := by
        calc
          |(omega_p p h * z).re| ≤ ‖omega_p p h * z‖ := Complex.abs_re_le_norm _
          _ = ‖omega_p p h‖ * ‖z‖ := by simp [Complex.norm_mul]
      have h4 :
          2 * |β| * |(omega_p p h * z).re| ≤ 2 * |β| * (‖omega_p p h‖ * ‖z‖) := by
        gcongr
      have h5 :
          2 * |β| * (‖omega_p p h‖ * ‖z‖) ≤ 2 * |β| * (Cω * ‖z‖) := by
        gcongr
      have hlin' : 2 * β * (omega_p p h * z).re ≤ 2 * |β| * (Cω * ‖z‖) := by
        have : |2 * β * (omega_p p h * z).re| ≤ 2 * |β| * (Cω * ‖z‖) := by
          -- rewrite the LHS and use the bounds above
          -- (`simp` keeps the expression stable here)
          have : 2 * |β| * |(omega_p p h * z).re| ≤ 2 * |β| * (Cω * ‖z‖) := by
            exact (h4.trans (h5.trans_eq (by ring)))
          simpa [h2] using this
        exact h1.trans this
      have hYle : Y h ≤ CY := (le_trans (le_abs_self _) (hYb h))
      linarith
    have hexp :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
      -- `exp` is monotone
      simpa [arguinTaiWeight] using (Real.exp_le_exp.mpr hlin)
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    -- `‖w‖ = w` since `w>0`
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hexp
  exact MeasureTheory.Integrable.of_bound (μ := μ01) hmeas _ hbound

noncomputable def Z_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ h, arguinTaiWeight β p Y z h ∂μ01

lemma Z_p_pos_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    0 < Z_p β p Y z := by
  -- Use `integral_exp_pos` with `f h = 2*β*Re(ω_p(h)*z) + Y(h)`.
  have hint : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  -- `Z_p` is that integral.
  simpa [Z_p, arguinTaiWeight] using
    (MeasureTheory.integral_exp_pos (μ := μ01) (f := fun h => (2 * β) * (omega_p p h * z).re + Y h)
      (by
        -- match `Real.exp (f h)` with our `arguinTaiWeight`
        simpa [arguinTaiWeight] using hint))

lemma Z_p_ne_zero_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    Z_p β p Y z ≠ 0 :=
  (ne_of_gt (Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)))

noncomputable def N_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ h, (omega_p p h) * (arguinTaiWeight β p Y z h : ℂ) ∂μ01

/-- The Arguin–Tai function `F_p : ℂ → ℂ`. -/
noncomputable def F_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ :=
  (N_p β p Y z) / (Z_p β p Y z)

end

end SpinGlass
