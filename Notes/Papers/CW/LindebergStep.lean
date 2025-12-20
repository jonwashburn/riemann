import Notes.Papers.CW.Lindenberg
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped BigOperators
open scoped Nat

namespace Probability.Lindeberg

/-!
## One-step Lindeberg replacement (scalar)

This file isolates the *single replacement step* used in the CW/Arguin blockwise Lindeberg method.

Autoformalizer/IDS alignment:
- no new "heap" structures;
- state theorems on Mathlib primitives (`IndepFun`, `Integrable`, `ContDiff`);
- keep the result reusable: a mismatch-form lemma + a moment-matching corollary.
-/

section Scalar

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Deterministic inequality: `|x| ≤ 1 + |x|^3`. -/
lemma abs_le_one_add_abs_pow_three (x : ℝ) : |x| ≤ 1 + |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · nlinarith [hx, pow_nonneg (abs_nonneg x) (3 : ℕ)]
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    -- `|x| ≤ |x|^3` for `|x| ≥ 1`
    have hx2 : 1 ≤ |x| ^ (2 : ℕ) := by
      -- avoid `MulLeftMono` (not available for `ℝ`), use `mul_le_mul` with positivity.
      have hx0 : 0 ≤ |x| := le_trans (by norm_num) hx1
      have : (1 : ℝ) * 1 ≤ |x| * |x| := mul_le_mul hx1 hx1 (by norm_num) hx0
      simpa [pow_two] using this
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have : |x| * 1 ≤ |x| * (|x| ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hx2 hx0
    have : |x| ≤ |x| ^ (3 : ℕ) := by
      simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using this
    linarith

/-- Deterministic inequality: `|x^2| ≤ 1 + |x|^3`. -/
lemma abs_sq_le_one_add_abs_pow_three (x : ℝ) : |x ^ 2| ≤ 1 + |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · -- then `|x|^2 ≤ 1`
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hx2 : |x| ^ (2 : ℕ) ≤ |x| := by
      -- multiply `|x| ≤ 1` by `|x| ≥ 0`
      simpa [pow_two, mul_assoc] using (mul_le_mul_of_nonneg_left hx hx0)
    have : |x| ^ (2 : ℕ) ≤ (1 : ℝ) := le_trans hx2 hx
    -- `|x^2| = |x|^2`
    have : |x ^ 2| ≤ (1 : ℝ) := by simpa [abs_pow] using this
    linarith [this, pow_nonneg (abs_nonneg x) (3 : ℕ)]
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hx2 : 0 ≤ |x| ^ (2 : ℕ) := by positivity
    have : (|x| ^ (2 : ℕ)) * 1 ≤ (|x| ^ (2 : ℕ)) * |x| :=
      mul_le_mul_of_nonneg_left hx1 hx2
    have : |x| ^ (2 : ℕ) ≤ |x| ^ (3 : ℕ) := by
      simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using this
    have : |x ^ 2| ≤ |x| ^ (3 : ℕ) := by
      simpa [abs_pow] using this
    linarith

/-- If `|X|^3` is integrable, then `|X|` is integrable (assuming measurability). -/
lemma integrable_abs_of_integrable_abs_pow_three {X : Ω → ℝ}
    (hX : Measurable X)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P) :
    Integrable (fun ω => |X ω|) P := by
  have hint : Integrable (fun ω => (1 : ℝ) + |X ω| ^ 3) P :=
    (integrable_const (μ := P) (1 : ℝ)).add hX3
  refine Integrable.mono' (f := fun ω => |X ω|) (g := fun ω => (1 : ℝ) + |X ω| ^ 3)
    hint (by
      -- avoid relying on `Measurable.abs`; use `‖X‖` measurability.
      simpa [Real.norm_eq_abs] using (hX.aestronglyMeasurable.norm : AEStronglyMeasurable (fun ω => ‖X ω‖) P)) ?_
  refine ae_of_all _ (fun ω => ?_)
  -- `‖ |X| ‖ = |X|` on `ℝ`
  simpa [Real.norm_eq_abs, abs_abs] using (abs_le_one_add_abs_pow_three (X ω))

/-- If `|X|^3` is integrable, then `X^2` is integrable (assuming measurability). -/
lemma integrable_sq_of_integrable_abs_pow_three {X : Ω → ℝ}
    (hX : Measurable X)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P) :
    Integrable (fun ω => (X ω) ^ 2) P := by
  have hint : Integrable (fun ω => (1 : ℝ) + |X ω| ^ 3) P :=
    (integrable_const (μ := P) (1 : ℝ)).add hX3
  refine Integrable.mono' (f := fun ω => (X ω) ^ 2) (g := fun ω => (1 : ℝ) + |X ω| ^ 3)
    hint ((hX.pow_const 2).aestronglyMeasurable) ?_
  refine ae_of_all _ (fun ω => ?_)
  simpa [Real.norm_eq_abs] using (abs_sq_le_one_add_abs_pow_three (X ω))

/-- If `|X|^3` is integrable, then `X` is integrable (assuming measurability). -/
lemma integrable_of_integrable_abs_pow_three {X : Ω → ℝ}
    (hX : Measurable X)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P) :
    Integrable X P := by
  have habs : Integrable (fun ω => |X ω|) P :=
    integrable_abs_of_integrable_abs_pow_three (P := P) hX hX3
  have hXae : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have : Integrable (fun ω => ‖X ω‖) P := by
    simpa [Real.norm_eq_abs] using habs
  exact (integrable_norm_iff (μ := P) (f := X) hXae).1 this

/-- Integrability of a uniformly bounded measurable function on a probability space. -/
lemma integrable_of_bounded {f : Ω → ℝ} {C : ℝ}
    (hf : Measurable f)
    (hbound : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f P := by
  have hint : Integrable (fun _ : Ω => C) P := integrable_const (μ := P) C
  refine Integrable.mono' (f := f) (g := fun _ => C)
    hint (hf.aestronglyMeasurable) ?_
  exact ae_of_all _ hbound

-- The proof of the main one-step bound is long and can be heartbeat-heavy.
set_option maxHeartbeats 800000

/-- One-step scalar replacement bound (moment-mismatch form).

This is the analytic heart of the CW/Arguin blockwise replacement method.

It isolates the dependency on the test function `phi` through uniform bounds on
`phi'`, `phi''`, `phi'''` and controls the remainder by third moments.
-/
theorem lindeberg_step_scalar_bound
    {U X Y : Ω → ℝ}
    (hUX : U ⟂ᵢ[P] X) (hUY : U ⟂ᵢ[P] Y)
    (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    {phi : ℝ → ℝ} {A0 A1 A2 M : ℝ}
    (hphi : ContDiff ℝ 3 phi)
    (hA0 : ∀ x, |phi x| ≤ A0)
    (hA1 : ∀ x, |deriv phi x| ≤ A1)
    (hA2 : ∀ x, |iteratedDeriv 2 phi x| ≤ A2)
    (hM : ∀ x, |iteratedDeriv 3 phi x| ≤ M)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P)
    (hY3 : Integrable (fun ω => |Y ω| ^ 3) P) :
    |(∫ ω, phi (U ω + X ω) ∂P) - (∫ ω, phi (U ω + Y ω) ∂P)|
      ≤ A1 * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)|
        + ((1 + 1 : ℝ)⁻¹) * A2 * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)|
        + (M / 6) * ((∫ ω, |X ω| ^ 3 ∂P) + (∫ ω, |Y ω| ^ 3 ∂P)) := by
  classical

  -- Integrability of `X, Y, X^2, Y^2` from third moments.
  have hX_int : Integrable X P :=
    integrable_of_integrable_abs_pow_three (P := P) hX hX3
  have hY_int : Integrable Y P :=
    integrable_of_integrable_abs_pow_three (P := P) hY hY3
  have hX2_int : Integrable (fun ω => (X ω) ^ 2) P :=
    integrable_sq_of_integrable_abs_pow_three (P := P) hX hX3
  have hY2_int : Integrable (fun ω => (Y ω) ^ 2) P :=
    integrable_sq_of_integrable_abs_pow_three (P := P) hY hY3

  -- Measurability of derivatives.
  have hmeas_deriv : Measurable (deriv phi) := by
    have hcont : Continuous (iteratedDeriv 1 phi) :=
      hphi.continuous_iteratedDeriv 1 (by decide : (1 : WithTop ℕ∞) ≤ 3)
    simpa [iteratedDeriv_one] using hcont.measurable
  have hmeas_deriv2 : Measurable (iteratedDeriv 2 phi) := by
    have hcont : Continuous (iteratedDeriv 2 phi) :=
      hphi.continuous_iteratedDeriv 2 (by decide : (2 : WithTop ℕ∞) ≤ 3)
    exact hcont.measurable

  -- Taylor coefficients along `U`.
  let a : Ω → ℝ := fun ω => deriv phi (U ω)
  let b : Ω → ℝ := fun ω => ((1 + 1 : ℝ)⁻¹) * iteratedDeriv 2 phi (U ω)

  have ha_meas : Measurable a := hmeas_deriv.comp hU
  have hb_meas : Measurable b := (measurable_const.mul (hmeas_deriv2.comp hU))

  have ha_int : Integrable a P :=
    integrable_of_bounded (P := P) ha_meas (fun ω => by
      simpa [a, Real.norm_eq_abs] using hA1 (U ω))
  have hb_int : Integrable b P := by
    refine integrable_of_bounded (P := P) (C := ((1 + 1 : ℝ)⁻¹) * A2) hb_meas ?_
    intro ω
    have h2 : |iteratedDeriv 2 phi (U ω)| ≤ A2 := hA2 (U ω)
    -- Avoid `simp [abs_of_nonneg (by positivity)]` (it can leave typeclass metavariables).
    have hc0 : 0 ≤ ((1 + 1 : ℝ)⁻¹) := by positivity
    have habsc : |((1 + 1 : ℝ)⁻¹)| = ((1 + 1 : ℝ)⁻¹) := abs_of_nonneg hc0
    calc
      ‖b ω‖
          = |((1 + 1 : ℝ)⁻¹)| * |iteratedDeriv 2 phi (U ω)| := by
              -- `‖·‖` on `ℝ` is `abs`
              simp [b, Real.norm_eq_abs]
      _ ≤ ((1 + 1 : ℝ)⁻¹) * A2 := by
            simpa [habsc, mul_assoc] using (mul_le_mul_of_nonneg_left h2 hc0)

  -- Factorization via independence.
  have hind_aX : (a ⟂ᵢ[P] X) := by
    simpa [a] using (IndepFun.comp (μ := P) (f := U) (g := X) hUX hmeas_deriv measurable_id)
  have hind_aY : (a ⟂ᵢ[P] Y) := by
    simpa [a] using (IndepFun.comp (μ := P) (f := U) (g := Y) hUY hmeas_deriv measurable_id)
  have hind_bX2 : (b ⟂ᵢ[P] fun ω => (X ω) ^ 2) := by
    have hsq : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
    have hbU : Measurable (fun u => ((1 + 1 : ℝ)⁻¹) * iteratedDeriv 2 phi u) :=
      measurable_const.mul hmeas_deriv2
    simpa [b] using (IndepFun.comp (μ := P) (f := U) (g := X) hUX hbU hsq)
  have hind_bY2 : (b ⟂ᵢ[P] fun ω => (Y ω) ^ 2) := by
    have hsq : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
    have hbU : Measurable (fun u => ((1 + 1 : ℝ)⁻¹) * iteratedDeriv 2 phi u) :=
      measurable_const.mul hmeas_deriv2
    simpa [b] using (IndepFun.comp (μ := P) (f := U) (g := Y) hUY hbU hsq)

  have hfac_aX : (∫ ω, a ω * X ω ∂P) = (∫ ω, a ω ∂P) * (∫ ω, X ω ∂P) := by
    simpa using
      (IndepFun.integral_fun_mul_eq_mul_integral (μ := P) hind_aX ha_int.aestronglyMeasurable hX.aestronglyMeasurable)
  have hfac_aY : (∫ ω, a ω * Y ω ∂P) = (∫ ω, a ω ∂P) * (∫ ω, Y ω ∂P) := by
    simpa using
      (IndepFun.integral_fun_mul_eq_mul_integral (μ := P) hind_aY ha_int.aestronglyMeasurable hY.aestronglyMeasurable)
  have hfac_bX2 : (∫ ω, b ω * (X ω) ^ 2 ∂P) = (∫ ω, b ω ∂P) * (∫ ω, (X ω) ^ 2 ∂P) := by
    simpa using
      (IndepFun.integral_fun_mul_eq_mul_integral (μ := P) hind_bX2 hb_int.aestronglyMeasurable hX2_int.aestronglyMeasurable)
  have hfac_bY2 : (∫ ω, b ω * (Y ω) ^ 2 ∂P) = (∫ ω, b ω ∂P) * (∫ ω, (Y ω) ^ 2 ∂P) := by
    simpa using
      (IndepFun.integral_fun_mul_eq_mul_integral (μ := P) hind_bY2 hb_int.aestronglyMeasurable hY2_int.aestronglyMeasurable)

  -- Remainders.
  let RX : Ω → ℝ := fun ω =>
    phi (U ω + X ω) - (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2)
  let RY : Ω → ℝ := fun ω =>
    phi (U ω + Y ω) - (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2)

  have hRX : |∫ ω, RX ω ∂P| ≤ (M / 6) * ∫ ω, |X ω| ^ 3 ∂P := by
    simpa [RX, a, b, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      using (abs_integral_quadraticRemainder_le (P := P) (U := U) (X := X)
        (phi := phi) (M := M) hphi hM hX3)
  have hRY : |∫ ω, RY ω ∂P| ≤ (M / 6) * ∫ ω, |Y ω| ^ 3 ∂P := by
    simpa [RY, a, b, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      using (abs_integral_quadraticRemainder_le (P := P) (U := U) (X := Y)
        (phi := phi) (M := M) hphi hM hY3)

  -- Integrability of bounded terms.
  have hInt_phiU : Integrable (fun ω => phi (U ω)) P :=
    integrable_of_bounded (P := P) ((hphi.continuous.measurable).comp hU) (fun ω => by
      simpa [Real.norm_eq_abs] using hA0 (U ω))
  have hInt_phiUX : Integrable (fun ω => phi (U ω + X ω)) P := by
    have hmeas : Measurable (fun ω => U ω + X ω) := hU.add hX
    exact integrable_of_bounded (P := P) ((hphi.continuous.measurable).comp hmeas) (fun ω => by
      simpa [Real.norm_eq_abs] using hA0 (U ω + X ω))
  have hInt_phiUY : Integrable (fun ω => phi (U ω + Y ω)) P := by
    have hmeas : Measurable (fun ω => U ω + Y ω) := hU.add hY
    exact integrable_of_bounded (P := P) ((hphi.continuous.measurable).comp hmeas) (fun ω => by
      simpa [Real.norm_eq_abs] using hA0 (U ω + Y ω))

  -- Products are integrable because `a,b` are bounded and `X,Y` have finite moments.
  have ha_bound : ∀ ω, |a ω| ≤ A1 := fun ω => by simpa [a] using hA1 (U ω)
  have hb_bound : ∀ ω, |b ω| ≤ ((1 + 1 : ℝ)⁻¹) * A2 := fun ω => by
    have h2 : |iteratedDeriv 2 phi (U ω)| ≤ A2 := hA2 (U ω)
    have hc0 : 0 ≤ ((1 + 1 : ℝ)⁻¹) := by positivity
    have habsc : |((1 + 1 : ℝ)⁻¹)| = ((1 + 1 : ℝ)⁻¹) := abs_of_nonneg hc0
    calc
      |b ω| = |((1 + 1 : ℝ)⁻¹)| * |iteratedDeriv 2 phi (U ω)| := by
                simp [b, abs_mul]
      _ ≤ ((1 + 1 : ℝ)⁻¹) * A2 := by
            simpa [habsc, mul_assoc] using (mul_le_mul_of_nonneg_left h2 hc0)

  have hInt_aX : Integrable (fun ω => a ω * X ω) P := by
    have hdom : Integrable (fun ω => A1 * ‖X ω‖) P := (hX_int.norm.const_mul A1)
    have hmeas : AEStronglyMeasurable (fun ω => a ω * X ω) P :=
      ((ha_meas.mul hX).aestronglyMeasurable)
    refine Integrable.mono' hdom hmeas ?_
    refine ae_of_all _ (fun ω => ?_)
    -- `‖a*X‖ = |a|*‖X‖ ≤ A1*‖X‖`
    simpa [Real.norm_eq_abs, abs_mul, mul_assoc] using
      (mul_le_mul_of_nonneg_right (ha_bound ω) (norm_nonneg (X ω)))

  have hInt_aY : Integrable (fun ω => a ω * Y ω) P := by
    have hdom : Integrable (fun ω => A1 * ‖Y ω‖) P := (hY_int.norm.const_mul A1)
    have hmeas : AEStronglyMeasurable (fun ω => a ω * Y ω) P :=
      ((ha_meas.mul hY).aestronglyMeasurable)
    refine Integrable.mono' hdom hmeas ?_
    refine ae_of_all _ (fun ω => ?_)
    simpa [Real.norm_eq_abs, abs_mul, mul_assoc] using
      (mul_le_mul_of_nonneg_right (ha_bound ω) (norm_nonneg (Y ω)))

  have hInt_bX2 : Integrable (fun ω => b ω * (X ω) ^ 2) P := by
    have hdom : Integrable (fun ω => (((1 + 1 : ℝ)⁻¹) * A2) * ‖(X ω) ^ 2‖) P :=
      (hX2_int.norm.const_mul (((1 + 1 : ℝ)⁻¹) * A2))
    have hmeas : AEStronglyMeasurable (fun ω => b ω * (X ω) ^ 2) P :=
      ((hb_meas.mul (hX.pow_const 2)).aestronglyMeasurable)
    refine Integrable.mono' hdom hmeas ?_
    refine ae_of_all _ (fun ω => ?_)
    -- `‖b * X^2‖ = |b * X^2| = |b| * |X^2| ≤ ((1/2)*A2) * |X^2| = ((1/2)*A2) * ‖X^2‖`.
    have hmul : |b ω| * |(X ω) ^ 2| ≤ (((1 + 1 : ℝ)⁻¹) * A2) * |(X ω) ^ 2| :=
      mul_le_mul_of_nonneg_right (hb_bound ω) (abs_nonneg ((X ω) ^ 2))
    -- rewrite `|b|*|X^2|` as `|b*X^2|`.
    have : |b ω * (X ω) ^ 2| ≤ (((1 + 1 : ℝ)⁻¹) * A2) * |(X ω) ^ 2| := by
      simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    simpa [Real.norm_eq_abs, abs_mul, mul_assoc] using this

  have hInt_bY2 : Integrable (fun ω => b ω * (Y ω) ^ 2) P := by
    have hdom : Integrable (fun ω => (((1 + 1 : ℝ)⁻¹) * A2) * ‖(Y ω) ^ 2‖) P :=
      (hY2_int.norm.const_mul (((1 + 1 : ℝ)⁻¹) * A2))
    have hmeas : AEStronglyMeasurable (fun ω => b ω * (Y ω) ^ 2) P :=
      ((hb_meas.mul (hY.pow_const 2)).aestronglyMeasurable)
    refine Integrable.mono' hdom hmeas ?_
    refine ae_of_all _ (fun ω => ?_)
    have hmul : |b ω| * |(Y ω) ^ 2| ≤ (((1 + 1 : ℝ)⁻¹) * A2) * |(Y ω) ^ 2| :=
      mul_le_mul_of_nonneg_right (hb_bound ω) (abs_nonneg ((Y ω) ^ 2))
    have : |b ω * (Y ω) ^ 2| ≤ (((1 + 1 : ℝ)⁻¹) * A2) * |(Y ω) ^ 2| := by
      simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    simpa [Real.norm_eq_abs, abs_mul, mul_assoc] using this

  -- Integrability of remainders from the pointwise remainder bound.
  have hInt_RX : Integrable RX P := by
    have hdom : Integrable (fun ω => (M / 6) * |X ω| ^ 3) P := hX3.const_mul (M / 6)
    have hmeasRX : Measurable RX := by
      -- measurable combination of measurable pieces
      have hmeas_phi : Measurable phi := hphi.continuous.measurable
      fun_prop
    refine Integrable.mono' (f := RX) (g := fun ω => (M / 6) * |X ω| ^ 3)
      hdom (hmeasRX.aestronglyMeasurable) ?_
    refine ae_of_all _ (fun ω => ?_)
    have := abs_sub_quadraticTaylor_le (phi := phi) (M := M) (u := U ω) (z := X ω) hphi hM
    have : |RX ω| ≤ (M * |X ω| ^ 3) / 6 := by
      simpa [RX, a, b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm] using this
    -- rewrite `M*|X|^3/6` as `(M/6)*|X|^3`
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  have hInt_RY : Integrable RY P := by
    have hdom : Integrable (fun ω => (M / 6) * |Y ω| ^ 3) P := hY3.const_mul (M / 6)
    have hmeasRY : Measurable RY := by
      have hmeas_phi : Measurable phi := hphi.continuous.measurable
      fun_prop
    refine Integrable.mono' (f := RY) (g := fun ω => (M / 6) * |Y ω| ^ 3)
      hdom (hmeasRY.aestronglyMeasurable) ?_
    refine ae_of_all _ (fun ω => ?_)
    have := abs_sub_quadraticTaylor_le (phi := phi) (M := M) (u := U ω) (z := Y ω) hphi hM
    have : |RY ω| ≤ (M * |Y ω| ^ 3) / 6 := by
      simpa [RY, a, b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm] using this
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  -- Decompose expectations into polynomial + remainder.
  have hdecompX :
      (∫ ω, phi (U ω + X ω) ∂P)
        = (∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P) + (∫ ω, RX ω ∂P) := by
    have hInt_poly : Integrable (fun ω => phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) P := by
      simpa [add_assoc] using (hInt_phiU.add (hInt_aX.add hInt_bX2))
    have hpoint : (fun ω => phi (U ω + X ω)) = fun ω => (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) + RX ω := by
      funext ω
      simp [RX, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      (∫ ω, phi (U ω + X ω) ∂P) = ∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) + RX ω ∂P := by
        simp [hpoint]
      _ = (∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P) + (∫ ω, RX ω ∂P) := by
        simpa using integral_add hInt_poly hInt_RX

  have hdecompY :
      (∫ ω, phi (U ω + Y ω) ∂P)
        = (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P) + (∫ ω, RY ω ∂P) := by
    have hInt_poly : Integrable (fun ω => phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) P := by
      simpa [add_assoc] using (hInt_phiU.add (hInt_aY.add hInt_bY2))
    have hpoint : (fun ω => phi (U ω + Y ω)) = fun ω => (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) + RY ω := by
      funext ω
      simp [RY, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      (∫ ω, phi (U ω + Y ω) ∂P) = ∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) + RY ω ∂P := by
        simp [hpoint]
      _ = (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P) + (∫ ω, RY ω ∂P) := by
        simpa using integral_add hInt_poly hInt_RY

  -- Polynomial difference in terms of moment mismatches.
  have hpoly :
      (∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P)
        - (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P)
      = (∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
        + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)) := by
    -- Expand each integral into the sum of three integrals (grouped to avoid simp blowups).
    have hIX :
        (∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P)
          = (∫ ω, phi (U ω) ∂P) + (∫ ω, a ω * X ω ∂P) + (∫ ω, b ω * (X ω) ^ 2 ∂P) := by
      have hInt12 : Integrable (fun ω => phi (U ω) + a ω * X ω) P := hInt_phiU.add hInt_aX
      have hInt123 : Integrable (fun ω => (phi (U ω) + a ω * X ω) + b ω * (X ω) ^ 2) P :=
        hInt12.add hInt_bX2
      calc
        (∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P)
            = ∫ ω, (phi (U ω) + a ω * X ω) + b ω * (X ω) ^ 2 ∂P := by
                simp [add_assoc]
        _ = (∫ ω, (phi (U ω) + a ω * X ω) ∂P) + (∫ ω, b ω * (X ω) ^ 2 ∂P) := by
              simpa using (integral_add hInt12 hInt_bX2)
        _ = (∫ ω, phi (U ω) ∂P) + (∫ ω, a ω * X ω ∂P) + (∫ ω, b ω * (X ω) ^ 2 ∂P) := by
              -- expand the first integral once more
              simp [integral_add, hInt_phiU, hInt_aX, add_assoc]
    have hIY :
        (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P)
          = (∫ ω, phi (U ω) ∂P) + (∫ ω, a ω * Y ω ∂P) + (∫ ω, b ω * (Y ω) ^ 2 ∂P) := by
      have hInt12 : Integrable (fun ω => phi (U ω) + a ω * Y ω) P := hInt_phiU.add hInt_aY
      calc
        (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P)
            = ∫ ω, (phi (U ω) + a ω * Y ω) + b ω * (Y ω) ^ 2 ∂P := by
                simp [add_assoc]
        _ = (∫ ω, (phi (U ω) + a ω * Y ω) ∂P) + (∫ ω, b ω * (Y ω) ^ 2 ∂P) := by
              simpa using (integral_add hInt12 hInt_bY2)
        _ = (∫ ω, phi (U ω) ∂P) + (∫ ω, a ω * Y ω ∂P) + (∫ ω, b ω * (Y ω) ^ 2 ∂P) := by
              simp [integral_add, hInt_phiU, hInt_aY, add_assoc]
    -- Now subtract and factor using the independence equalities.
    calc
      (∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P)
          - (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P)
          = ((∫ ω, phi (U ω) ∂P) + (∫ ω, a ω * X ω ∂P) + (∫ ω, b ω * (X ω) ^ 2 ∂P))
              - ((∫ ω, phi (U ω) ∂P) + (∫ ω, a ω * Y ω ∂P) + (∫ ω, b ω * (Y ω) ^ 2 ∂P)) := by
              simp [hIX, hIY]
      _ = ((∫ ω, a ω * X ω ∂P) - (∫ ω, a ω * Y ω ∂P))
            + ((∫ ω, b ω * (X ω) ^ 2 ∂P) - (∫ ω, b ω * (Y ω) ^ 2 ∂P)) := by
              ring
      _ = (∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
            + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)) := by
              -- factor each difference using `hfac_*` and then regroup.
              simp [hfac_aX, hfac_aY, hfac_bX2, hfac_bY2]
              ring

  -- Bound `|∫ a|` and `|∫ b|` by the uniform bounds.
  have hA1_int : |∫ ω, a ω ∂P| ≤ A1 := by
    have habs : |∫ ω, a ω ∂P| ≤ ∫ ω, |a ω| ∂P :=
      abs_integral_le_integral_abs (μ := P) (f := a)
    have hle : (fun ω => |a ω|) ≤ᵐ[P] fun _ => A1 :=
      ae_of_all _ (fun ω => by simpa [a] using hA1 (U ω))
    have : ∫ ω, |a ω| ∂P ≤ ∫ _ : Ω, A1 ∂P :=
      integral_mono_of_nonneg (μ := P) (ae_of_all _ (fun _ => abs_nonneg _))
        (integrable_const (μ := P) A1) hle
    have : ∫ ω, |a ω| ∂P ≤ A1 := by simpa using (this.trans_eq (by simp))
    exact habs.trans this

  have hA2_int : |∫ ω, b ω ∂P| ≤ ((1 + 1 : ℝ)⁻¹) * A2 := by
    have habs : |∫ ω, b ω ∂P| ≤ ∫ ω, |b ω| ∂P :=
      abs_integral_le_integral_abs (μ := P) (f := b)
    have hle : (fun ω => |b ω|) ≤ᵐ[P] fun _ => ((1 + 1 : ℝ)⁻¹) * A2 :=
      ae_of_all _ (fun ω => hb_bound ω)
    have : ∫ ω, |b ω| ∂P ≤ ∫ _ : Ω, ((1 + 1 : ℝ)⁻¹) * A2 ∂P :=
      integral_mono_of_nonneg (μ := P) (ae_of_all _ (fun _ => abs_nonneg _))
        (integrable_const (μ := P) _) hle
    have : ∫ ω, |b ω| ∂P ≤ ((1 + 1 : ℝ)⁻¹) * A2 := by
      simpa using (this.trans_eq (by simp))
    exact habs.trans this

  -- Assemble the final bound.
  have hdiff :
      (∫ ω, phi (U ω + X ω) ∂P) - (∫ ω, phi (U ω + Y ω) ∂P)
        = ((∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
            + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)))
          + ((∫ ω, RX ω ∂P) - (∫ ω, RY ω ∂P)) := by
    -- Avoid `simp` here (it can trigger large definitional reductions); use `rw` + `ring`.
    -- Rewrite both expectations using the decompositions, then regroup.
    calc
      (∫ ω, phi (U ω + X ω) ∂P) - (∫ ω, phi (U ω + Y ω) ∂P)
          = ((∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P) + (∫ ω, RX ω ∂P))
              - ((∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P) + (∫ ω, RY ω ∂P)) := by
                rw [hdecompX, hdecompY]
      _ = ((∫ ω, (phi (U ω) + a ω * X ω + b ω * (X ω) ^ 2) ∂P)
              - (∫ ω, (phi (U ω) + a ω * Y ω + b ω * (Y ω) ^ 2) ∂P))
            + ((∫ ω, RX ω ∂P) - (∫ ω, RY ω ∂P)) := by
                ring
      _ = ((∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
            + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)))
            + ((∫ ω, RX ω ∂P) - (∫ ω, RY ω ∂P)) := by
                simp [hpoly]

  calc
    |(∫ ω, phi (U ω + X ω) ∂P) - (∫ ω, phi (U ω + Y ω) ∂P)|
        = |((∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
              + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)))
            + ((∫ ω, RX ω ∂P) - (∫ ω, RY ω ∂P))| := by
            simp [hdiff]
    _ ≤ |(∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
            + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P))|
          + |(∫ ω, RX ω ∂P) - (∫ ω, RY ω ∂P)| := by
            simpa using abs_add_le _ _
    _ ≤ (|(∫ ω, a ω ∂P)| * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)|
          + |(∫ ω, b ω ∂P)| * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)|)
        + (|∫ ω, RX ω ∂P| + |∫ ω, RY ω ∂P|) := by
          have hab :
              |(∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P))
                  + (∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P))|
                ≤ |∫ ω, a ω ∂P| * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)|
                  + |∫ ω, b ω ∂P| * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)| := by
            -- triangle + multiplicativity of abs
            simpa [abs_mul] using
              (abs_add_le
                ((∫ ω, a ω ∂P) * ((∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)))
                ((∫ ω, b ω ∂P) * ((∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P))))
          have hrem :
              |(∫ ω, RX ω ∂P) - (∫ ω, RY ω ∂P)| ≤ |∫ ω, RX ω ∂P| + |∫ ω, RY ω ∂P| := by
            -- `|x - y| = |x + (-y)| ≤ |x| + |y|`
            simpa [sub_eq_add_neg] using (abs_add_le (∫ ω, RX ω ∂P) (-(∫ ω, RY ω ∂P)))
          nlinarith [hab, hrem]
    _ ≤ (A1 * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)|
          + ((1 + 1 : ℝ)⁻¹) * A2 * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)|)
        + (M / 6) * ((∫ ω, |X ω| ^ 3 ∂P) + (∫ ω, |Y ω| ^ 3 ∂P)) := by
          have hrem : |∫ ω, RX ω ∂P| + |∫ ω, RY ω ∂P|
              ≤ (M / 6) * ((∫ ω, |X ω| ^ 3 ∂P) + (∫ ω, |Y ω| ^ 3 ∂P)) := by
            nlinarith [hRX, hRY]
          have hcoef1 :
              |∫ ω, a ω ∂P| * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)|
                ≤ A1 * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)| :=
            mul_le_mul_of_nonneg_right hA1_int (abs_nonneg _)
          have hcoef2 :
              |∫ ω, b ω ∂P| * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)|
                ≤ ((1 + 1 : ℝ)⁻¹) * A2 * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)| :=
            mul_le_mul_of_nonneg_right hA2_int (abs_nonneg _)
          nlinarith [hcoef1, hcoef2, hrem]
    _ = A1 * |(∫ ω, X ω ∂P) - (∫ ω, Y ω ∂P)|
        + ((1 + 1 : ℝ)⁻¹) * A2 * |(∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, (Y ω) ^ 2 ∂P)|
        + (M / 6) * ((∫ ω, |X ω| ^ 3 ∂P) + (∫ ω, |Y ω| ^ 3 ∂P)) := by
          ring

set_option maxHeartbeats 200000

/-- One-step scalar replacement bound assuming matching first two moments.

This is the form used directly in CW/Arguin telescoping.
-/
theorem lindeberg_step_scalar
    {U X Y : Ω → ℝ}
    (hUX : U ⟂ᵢ[P] X) (hUY : U ⟂ᵢ[P] Y)
    (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    {phi : ℝ → ℝ} {A0 A1 A2 M : ℝ}
    (hphi : ContDiff ℝ 3 phi)
    (hA0 : ∀ x, |phi x| ≤ A0)
    (hA1 : ∀ x, |deriv phi x| ≤ A1)
    (hA2 : ∀ x, |iteratedDeriv 2 phi x| ≤ A2)
    (hM : ∀ x, |iteratedDeriv 3 phi x| ≤ M)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P)
    (hY3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (hEX : (∫ ω, X ω ∂P) = (∫ ω, Y ω ∂P))
    (hEX2 : (∫ ω, (X ω) ^ 2 ∂P) = (∫ ω, (Y ω) ^ 2 ∂P)) :
    |(∫ ω, phi (U ω + X ω) ∂P) - (∫ ω, phi (U ω + Y ω) ∂P)|
      ≤ (M / 6) * ((∫ ω, |X ω| ^ 3 ∂P) + (∫ ω, |Y ω| ^ 3 ∂P)) := by
  have h :=
    lindeberg_step_scalar_bound (P := P) (U := U) (X := X) (Y := Y)
      hUX hUY hU hX hY (phi := phi)
      hphi hA0 hA1 hA2 hM hX3 hY3
  -- kill mismatch terms
  simpa [hEX, hEX2] using h

end Scalar

end Probability.Lindeberg
