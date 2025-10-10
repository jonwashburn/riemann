import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import rh.academic_framework.CompletedXi
import rh.academic_framework.DiskHardy
import rh.RS.Det2Outer
import rh.RS.PoissonAI
import rh.RS.Cayley

/-!
# Half-plane Outer Functions (Clean Rewrite)

This module provides a clean interface for outer functions on the right half-plane
Ω = {s : ℂ | Re s > 1/2}. We establish:

1. Basic definitions (domain, boundary, outer functions)
2. Poisson kernel and transport theorems
3. Boundary modulus matching
4. Pinch field specializations

The implementation focuses on clarity and avoids complex proof details where possible,
using interface predicates at the Prop level.
-/

namespace RH.AcademicFramework.HalfPlaneOuterV2

noncomputable section

open Complex MeasureTheory Filter
open scoped Real Topology

-- Import necessary symbols from other modules
open RH.AcademicFramework.CompletedXi
open RH.RS

/-! ## Section 1: Basic Definitions -/

/-- The right half-plane domain Ω = {s : ℂ | Re s > 1/2} -/
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

/-- Boundary parametrization of the critical line Re s = 1/2 -/
@[simp] def boundary (t : ℝ) : ℂ := (1/2 : ℝ) + I * (t : ℂ)

lemma boundary_re (t : ℝ) : (boundary t).re = 1/2 := by simp [boundary]

lemma boundary_im (t : ℝ) : (boundary t).im = t := by simp [boundary]

@[simp] lemma boundary_mk_eq (t : ℝ) :
  boundary t = { re := (1/2 : ℝ), im := t } := by
  -- Prove equality by matching real and imaginary parts
  apply Complex.ext
  · simp [boundary]
  · simp [boundary]

/-- An outer function on Ω: analytic and non-vanishing -/
structure IsOuter (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonvanishing : ∀ s ∈ Ω, O s ≠ 0

/-- Boundary modulus equality: |O| = |F| on the critical line -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, abs (O (boundary t)) = abs (F (boundary t))

/-- Existence of an outer with prescribed boundary modulus -/
def ExistsOuterWithModulus (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuter O ∧ BoundaryModulusEq O F

/-! ## Section 2: Poisson Kernel and Integration -/

/-- The Poisson kernel for the right half-plane -/
@[simp] noncomputable def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  let a := z.re - 1/2
  let b := z.im
  (1 / Real.pi) * (a / (a^2 + (t - b)^2))

/-- Non-negativity of the Poisson kernel for z ∈ Ω -/
lemma poissonKernel_nonneg {z : ℂ} (hz : z ∈ Ω) (t : ℝ) :
    0 ≤ poissonKernel z t := by
  unfold poissonKernel Ω at *
  simp only [Set.mem_setOf_eq] at hz
  have ha : 0 < z.re - 1/2 := sub_pos.mpr hz
  have hdenom : 0 < (z.re - 1/2)^2 + (t - z.im)^2 := by
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_ne_zero (ne_of_gt ha)
    · exact sq_nonneg _
  exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
    (div_nonneg ha.le hdenom.le)

/-! ### Measurability helpers (placed early to be available downstream) -/

lemma measurable_boundary_affine : Measurable (boundary : ℝ → ℂ) := by
  unfold boundary
  apply Measurable.add
  · exact measurable_const
  · apply Measurable.const_mul
    exact Complex.continuous_ofReal.measurable

/-- Adapter: the RS boundary parametrization equals the AF boundary parametrization. -/
lemma rs_boundary_eq_af (t : ℝ) : RH.RS.boundary t = boundary t := by
  apply Complex.ext
  · simp [RH.RS.boundary, boundary]
  · simp [RH.RS.boundary, boundary]

/-- Adapter: record-form boundary equals AF boundary. -/
lemma mk_boundary_eq_af (t : ℝ) : ({ re := (1/2 : ℝ), im := t } : ℂ) = boundary t := by
  apply Complex.ext
  · simp [boundary]
  · simp [boundary]

lemma measurable_boundary_F_pinch
    {O : ℂ → ℂ}
    (hDet_meas : Measurable (fun t : ℝ => det2 (boundary t)))
    (hO_meas   : Measurable (fun t => O (boundary t)))
    (hXi_meas  : Measurable (fun t => riemannXi_ext (boundary t)))
    : Measurable (fun t => F_pinch det2 O (boundary t)) := by
  unfold F_pinch J_pinch
  -- F_pinch = 2 * J_pinch = 2 * (det2 / (O * ξ_ext))
  have h_denom : Measurable (fun t => O (boundary t) * riemannXi_ext (boundary t)) :=
    hO_meas.mul hXi_meas
  have h_ratio : Measurable (fun t => det2 (boundary t) / (O (boundary t) * riemannXi_ext (boundary t))) :=
    hDet_meas.div h_denom
  simpa using h_ratio.const_mul (2 : ℂ)

/-! ### Generic trace measurability on the boundary -/

/-- If `f : ℂ → α` is measurable (Borel), then its trace along the boundary
`t ↦ f(boundary t)` is measurable on `ℝ`. -/
lemma measurable_on_boundary_of_measurable {α} [MeasurableSpace α]
  {f : ℂ → α} (hf : Measurable f) :
  Measurable (fun t : ℝ => f (boundary t)) := by
  have hb : Measurable (boundary : ℝ → ℂ) := measurable_boundary_affine
  exact hf.comp hb

/-- Poisson integral: reconstructs interior values from boundary data -/
@[simp] noncomputable def poissonIntegral (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, u t * poissonKernel z t

/-- Boundary positivity condition (P+) -/
def BoundaryPositive (F : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re

/-- Poisson representation: F has a Poisson integral representation on Ω -/
structure HasPoissonRep (F : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ F Ω
  integrable : ∀ z ∈ Ω, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ Ω, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-! ## Section 3: Transport Theorems -/

/-- Poisson transport: boundary positivity implies interior positivity -/
theorem poissonTransport {F : ℂ → ℂ} (hRep : HasPoissonRep F) :
    BoundaryPositive F → ∀ z ∈ Ω, 0 ≤ (F z).re := by
  intro hBoundary z hz
  -- Use the Poisson representation
  rw [hRep.formula z hz]
  unfold poissonIntegral
  -- The integral of non-negative functions is non-negative
  apply integral_nonneg_of_ae
  filter_upwards [hBoundary] with t ht
  exact mul_nonneg ht (poissonKernel_nonneg hz t)

/-- Subset Poisson representation (for domains with excluded singularities) -/
structure HasPoissonRepOn (F : ℂ → ℂ) (S : Set ℂ) : Prop where
  subset : S ⊆ Ω
  analytic : AnalyticOn ℂ F S
  integrable : ∀ z ∈ S, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ S, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-- Transport on subsets -/
theorem poissonTransportOn {F : ℂ → ℂ} {S : Set ℂ} (hRep : HasPoissonRepOn F S) :
    BoundaryPositive F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hBoundary z hz
  rw [hRep.formula z hz]
  unfold poissonIntegral
  apply integral_nonneg_of_ae
  have hzΩ : z ∈ Ω := hRep.subset hz
  filter_upwards [hBoundary] with t ht
  exact mul_nonneg ht (poissonKernel_nonneg hzΩ t)

/-! ## Section 4: Pinch Field Specializations -/

/-- The pinch field F_pinch = 2 * J_pinch -/
@[simp] noncomputable def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ) * J_pinch det2 O z

/-- Analyticity of J_pinch on the off-zeros set -/
lemma J_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext Ω) :
    AnalyticOn ℂ (J_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- J_pinch = det2 / (O * ξ_ext) is analytic where the denominator is non-zero
  have h1 := hDet2.analytic
  have h2 := hO.analytic
  have h3 := hXi
  -- The denominator O * ξ_ext is non-zero on the off-zeros set
  have hdenom : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), O z * riemannXi_ext z ≠ 0 := by
    intro z hz
    simp only [Set.mem_diff, Set.mem_setOf_eq] at hz
    apply mul_ne_zero
    · exact hO.nonzero hz.1
    · exact hz.2
  -- Use analyticity of quotients where denominator is non-zero
  -- Restrict all functions to the off-zeros set
  have h1' : AnalyticOn ℂ det2 (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h1.mono; intro z hz; exact hz.1
  have h2' : AnalyticOn ℂ O (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h2.mono; intro z hz; exact hz.1
  have h3' : AnalyticOn ℂ riemannXi_ext (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h3.mono; intro z hz; exact hz.1
  apply AnalyticOn.div h1'
  · apply AnalyticOn.mul h2' h3'
  · exact hdenom

/-- Analyticity of F_pinch on the off-zeros set -/
lemma F_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext Ω) :
    AnalyticOn ℂ (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  unfold F_pinch
  -- F_pinch = 2 * J_pinch, so analyticity follows from J_pinch analyticity
  have hJ := J_pinch_analyticOn_offZeros hDet2 hO hXi
  have h2 : AnalyticOn ℂ (fun _ => (2 : ℂ)) (Ω \ {z | riemannXi_ext z = 0}) := analyticOn_const
  exact h2.mul hJ

/-- Boundary bound for F_pinch when boundary modulus equality holds -/
lemma F_pinch_boundary_bound
    {O : ℂ → ℂ}
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (t : ℝ) :
    |(F_pinch det2 O (boundary t)).re| ≤ 2 := by
  -- Handle the cases where O or ξ_ext might be zero at the boundary
  by_cases hO_ne : O (boundary t) ≠ 0
  · by_cases hXi_ne : riemannXi_ext (boundary t) ≠ 0
    · -- Both non-zero: use the RS lemma directly since boundaries are compatible
      -- Note: RH.RS.boundary and our boundary are definitionally equal
      have boundary_eq : ∀ u, RH.RS.boundary u = boundary u := by
        intro u
        simp only [RH.RS.boundary, boundary]
        norm_cast
        simp
      -- Create the BoundaryModulusEq for the RS module
      have hBME' : ∀ u, Complex.abs (O (RH.RS.boundary u)) =
                         Complex.abs ((det2 (RH.RS.boundary u)) / (riemannXi_ext (RH.RS.boundary u))) := by
        intro u
        rw [boundary_eq]
        exact hBME u
      -- Our hypotheses work with RS.boundary due to equality
      have hO_ne' : O (RH.RS.boundary t) ≠ 0 := by
        rw [boundary_eq]; exact hO_ne
      have hXi_ne' : riemannXi_ext (RH.RS.boundary t) ≠ 0 := by
        rw [boundary_eq]; exact hXi_ne
      -- Apply the RS lemma
      have h := RH.RS.boundary_Re_F_pinch_le_two hBME' t hO_ne' hXi_ne'
      -- The result applies to our F_pinch and boundary
      convert h using 2
      · simp only [RH.RS.F_pinch, F_pinch, RH.RS.J_pinch, J_pinch]
        rw [boundary_eq]
    · -- ξ_ext = 0 at boundary: J_pinch = det2/(O·ξ_ext) = det2/0 = 0
      push_neg at hXi_ne
      simp only [F_pinch, J_pinch, hXi_ne, mul_zero, div_zero, zero_mul,
                 Complex.zero_re, abs_zero]
      norm_num
  · -- O = 0 at boundary: J_pinch = det2/(O·ξ_ext) = det2/0 = 0
    push_neg at hO_ne
    simp only [F_pinch, J_pinch, hO_ne, zero_mul, div_zero, Complex.zero_re, abs_zero]
    norm_num

/-! ## Section 5: Integrability Helpers -/

/-- Helper lemma: Poisson kernel is bounded by C/(1+(t-b)²) -/
private lemma poissonKernel_bound (z : ℂ) (hz : z ∈ Ω) :
    ∃ C > 0, ∀ t : ℝ, poissonKernel z t ≤ C / (1 + (t - z.im)^2) := by
  unfold Ω at hz
  simp only [Set.mem_setOf_eq] at hz
  set a := z.re - 1/2 with ha_def
  have ha : 0 < a := sub_pos.mpr hz
  -- Take C = (1/π) * max(a, 1/a)
  use (1 / Real.pi) * max a (1/a)
  constructor
  · apply mul_pos
    · exact one_div_pos.mpr Real.pi_pos
    · exact lt_max_of_lt_left ha
  · intro t
    -- The inequality a/(a²+(t-b)²) ≤ C/(1+(t-b)²) follows by case analysis
    -- When a ≤ 1: use that a*(1+X) ≤ (1/a)*(a²+X) for X ≥ 0
    -- When a > 1: use that a*(1+X) ≤ a*(a²+X) for X ≥ 0
    -- Denominators are positive
    have hden1 : 0 < (1 + (t - z.im) ^ 2) := by
      have : 0 ≤ (t - z.im) ^ 2 := sq_nonneg _
      have : 0 < (1 : ℝ) + (t - z.im) ^ 2 := by exact add_pos_of_pos_of_nonneg (by norm_num) this
      simpa using this
    have hden2 : 0 < a ^ 2 + (t - z.im) ^ 2 := by
      have : 0 < a ^ 2 := by
        have : a ≠ 0 := ne_of_gt ha
        simpa [pow_two] using mul_self_pos.mpr this
      exact add_pos_of_pos_of_nonneg this (sq_nonneg _)
    -- Core algebraic inequality: a*(1+X) ≤ C0*(a²+X) with C0 = max a (1/a)
    have hcore : a * (1 + (t - z.im) ^ 2) ≤ (max a (1 / a)) * (a ^ 2 + (t - z.im) ^ 2) := by
      have hcases := le_total a (1 : ℝ)
      cases hcases with
      | inl hA_le_one =>
        -- C0 ≥ 1/a
        have hC0_ge : (1 / a) ≤ max a (1 / a) := by exact le_max_right _ _
        -- Show a*(1+X) ≤ (1/a)*(a²+X)
        have hstep : a * (1 + (t - z.im) ^ 2) ≤ (1 / a) * (a ^ 2 + (t - z.im) ^ 2) := by
          -- Use that a² ≤ 1 and (t - z.im)² ≥ 0
          have hXnn : 0 ≤ (t - z.im) ^ 2 := by exact sq_nonneg _
          have ha2_le_one : a ^ 2 ≤ (1 : ℝ) := by
            have : a ≤ 1 := hA_le_one
            have : a ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left (le_of_lt ha) this (2 : ℕ)
            simpa [one_pow] using this
          -- a²*(1+X) = a² + a²*X ≤ a² + X
          have hx : a ^ 2 * (t - z.im) ^ 2 ≤ (t - z.im) ^ 2 := by
            simpa [one_mul] using mul_le_mul_of_nonneg_right ha2_le_one hXnn
          have ineq : a ^ 2 * (1 + (t - z.im) ^ 2) ≤ a ^ 2 + (t - z.im) ^ 2 := by
            simpa [mul_add] using add_le_add_left hx (a ^ 2)
          -- Multiply by (1/a) ≥ 0
          have ha_pos : 0 < a := ha
          have : (1 / a) * (a ^ 2 * (1 + (t - z.im) ^ 2)) ≤ (1 / a) * (a ^ 2 + (t - z.im) ^ 2) := by
            exact mul_le_mul_of_nonneg_left ineq (one_div_nonneg.mpr (le_of_lt ha_pos))
          -- Simplify (1/a)*(a²*Y) = a*Y
          have ha_ne : a ≠ 0 := ne_of_gt ha_pos
          simpa [one_div, pow_two, mul_comm, mul_left_comm, mul_assoc, ha_ne] using this
        -- Monotonicity in the constant
        have hnonneg : 0 ≤ (a ^ 2 + (t - z.im) ^ 2) := le_of_lt hden2
        have hlift : (1 / a) * (a ^ 2 + (t - z.im) ^ 2) ≤ (max a (1 / a)) * (a ^ 2 + (t - z.im) ^ 2) :=
          mul_le_mul_of_nonneg_right hC0_ge hnonneg
        exact le_trans hstep hlift
      | inr h_one_le_A =>
        -- C0 ≥ a
        have hC0_ge : a ≤ max a (1 / a) := by exact le_max_left _ _
        -- Show a*(1+X) ≤ a*(a²+X) using 1 ≤ a²
        have hstep : a * (1 + (t - z.im) ^ 2) ≤ a * (a ^ 2 + (t - z.im) ^ 2) := by
          have : (1 : ℝ) ≤ a ^ 2 := by
            have : (1 : ℝ) ≤ a := h_one_le_A
            have : (1 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left (by norm_num : (0 : ℝ) ≤ 1) this (2 : ℕ)
            simpa [one_pow] using this
          have hx : (1 + (t - z.im) ^ 2) ≤ (a ^ 2 + (t - z.im) ^ 2) := by
            have hnn : 0 ≤ (t - z.im) ^ 2 := sq_nonneg _
            exact add_le_add_right this _
          exact mul_le_mul_of_nonneg_left hx (le_of_lt ha)
        -- Monotonicity in the constant
        have hnonneg : 0 ≤ (a ^ 2 + (t - z.im) ^ 2) := le_of_lt hden2
        have hlift : a * (a ^ 2 + (t - z.im) ^ 2) ≤ (max a (1 / a)) * (a ^ 2 + (t - z.im) ^ 2) :=
          mul_le_mul_of_nonneg_right hC0_ge hnonneg
        exact le_trans hstep hlift
    -- Turn hcore into the desired fractional inequality
    have hineq :
        (1 / Real.pi) * (a / (a ^ 2 + (t - z.im) ^ 2))
          ≤ (1 / Real.pi) * ((max a (1 / a)) / (1 + (t - z.im) ^ 2)) := by
      have hπnonneg : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
      have hposL : 0 < (a ^ 2 + (t - z.im) ^ 2) := hden2
      have hposR : 0 < (1 + (t - z.im) ^ 2) := hden1
      -- From hcore: a*(1+X) ≤ C0*(a^2+X)
      -- We want to derive: a/(a^2+X) ≤ C0/(1+X)
      have hfrac : a / (a ^ 2 + (t - z.im) ^ 2) ≤ (max a (1 / a)) / (1 + (t - z.im) ^ 2) := by
        -- Divide both sides of hcore by (a^2+X)*(1+X) which is positive
        have hdenom_pos : 0 < (a ^ 2 + (t - z.im) ^ 2) * (1 + (t - z.im) ^ 2) :=
          mul_pos hposL hposR
        have := div_le_div_of_nonneg_right hcore (le_of_lt hdenom_pos)
        -- Simplify: LHS = a*(1+X)/((a^2+X)*(1+X)) = a/(a^2+X)
        have lhs_simp : a * (1 + (t - z.im) ^ 2) / ((a ^ 2 + (t - z.im) ^ 2) * (1 + (t - z.im) ^ 2)) =
                        a / (a ^ 2 + (t - z.im) ^ 2) := by
          field_simp
          ring
        -- Simplify: RHS = C0*(a^2+X)/((a^2+X)*(1+X)) = C0/(1+X)
        have rhs_simp : (max a (1 / a)) * (a ^ 2 + (t - z.im) ^ 2) / ((a ^ 2 + (t - z.im) ^ 2) * (1 + (t - z.im) ^ 2)) =
                        (max a (1 / a)) / (1 + (t - z.im) ^ 2) := by
          field_simp
          ring
        rw [lhs_simp, rhs_simp] at this
        exact this
      exact mul_le_mul_of_nonneg_left hfrac hπnonneg
    -- Final rewrite to the C/(1+(t-b)²) shape
    -- poissonKernel z t = (1/π) * a / (a^2 + (t - z.im)^2) where a = z.re - 1/2
    -- We can now directly rewrite using a = z.re - 1/2
    simpa [poissonKernel, ha_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hineq

/-- Integrability of the Poisson kernel -/
lemma poissonKernel_integrable {z : ℂ} (hz : z ∈ Ω) :
    Integrable (fun t : ℝ => poissonKernel z t) := by
  -- Get the bound
  obtain ⟨C, hC_pos, hbound⟩ := poissonKernel_bound z hz
  -- The dominating function is integrable
  have h_dom : Integrable (fun t => C / (1 + (t - z.im)^2)) := by
    -- integrable_inv_one_add_sq gives integrability of 1/(1+t²)
    -- Translation and scaling preserve integrability
    have : Integrable (fun t : ℝ => 1 / (1 + (t - z.im) ^ 2)) := by
      simpa [sub_eq_add_neg, pow_two] using
        (integrable_inv_one_add_sq.comp_sub_right z.im)
    simpa [div_eq_mul_inv] using this.const_mul C
  -- Apply comparison
  refine h_dom.mono ?_ ?_
  · -- Measurability of poissonKernel
    -- Build from basic measurable operations
    have hb : Measurable (fun t : ℝ => t - z.im) := by
      simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
    have hden : Measurable (fun t : ℝ => (z.re - 1/2) ^ 2 + (t - z.im) ^ 2) :=
      measurable_const.add (hb.pow measurable_const)
    have hfrac : Measurable
        (fun t : ℝ => (z.re - 1/2) / ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2)) := by
      have : Measurable (fun t : ℝ => ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2)⁻¹) :=
        hden.inv
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this.const_mul (z.re - 1/2)
    have hmeas : Measurable
        (fun t : ℝ => (1 / Real.pi) *
          ((z.re - 1/2) / ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2))) :=
      hfrac.const_mul (1 / Real.pi)
    simpa [poissonKernel] using hmeas.aestronglyMeasurable
  · -- Pointwise bound using hbound and nonnegativity of the kernel
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    -- Show ‖poissonKernel z t‖ ≤ ‖C / (1 + (t - z.im)²)‖
    have hpk_norm : ‖poissonKernel z t‖ = poissonKernel z t := by
      rw [Real.norm_eq_abs, _root_.abs_of_nonneg hk_nonneg]
    rw [hpk_norm]
    have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
    have hden_pos : 0 < 1 + (t - z.im) ^ 2 := by
      apply add_pos_of_pos_of_nonneg
      · norm_num
      · exact sq_nonneg _
    have hquot_nonneg : 0 ≤ C / (1 + (t - z.im) ^ 2) :=
      div_nonneg hC_nonneg (le_of_lt hden_pos)
    have hC_norm : ‖C / (1 + (t - z.im) ^ 2)‖ = C / (1 + (t - z.im) ^ 2) := by
      rw [Real.norm_eq_abs, _root_.abs_of_nonneg hquot_nonneg]
    rw [hC_norm]
    exact hbound t

/-- Integrability with bounded boundary data
    Note: The measurability assumption `hMeas` is needed since F may not be continuous.
    For analytic functions, this follows from continuity. -/
lemma integrable_boundedBoundary
    (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
    (hz : z ∈ Ω)
    (hBound : ∀ t : ℝ, |(F (boundary t)).re| ≤ M)
    (hMeas : Measurable (fun t => (F (boundary t)).re)) :
    Integrable (fun t => (F (boundary t)).re * poissonKernel z t) := by
  -- The kernel is integrable
  have hker := poissonKernel_integrable hz

  -- M must be nonnegative since |F.re| ≥ 0
  have hM_nonneg : 0 ≤ M := by
    trans |(F (boundary 0)).re|
    · exact abs_nonneg _
    · exact hBound 0

  -- The dominating function M * poissonKernel is integrable
  have h_dom : Integrable (fun t => M * poissonKernel z t) := by
    exact Integrable.const_mul hker M

  -- Apply comparison test
  refine h_dom.mono ?_ ?_
  · -- Measurability
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · -- Measurability of F(boundary t).re - directly from hypothesis
      exact hMeas
    · -- Measurability of poissonKernel z t
      -- The Poisson kernel is continuous, hence measurable
      apply Continuous.measurable
      unfold poissonKernel
      apply Continuous.mul
      · exact continuous_const
      · apply Continuous.div
        · exact continuous_const
        · apply Continuous.add
          · exact continuous_const
          · apply Continuous.pow
            apply Continuous.sub
            · exact continuous_id
            · exact continuous_const
        · -- Denominator is nonzero
          intro t
          apply ne_of_gt
          apply add_pos_of_pos_of_nonneg
          · apply sq_pos_of_ne_zero
            have ha : 0 < z.re - 1/2 := sub_pos.mpr hz
            exact ne_of_gt ha
          · exact sq_nonneg _
  · -- Bound
    filter_upwards with t
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    -- We need to show: ‖(F (boundary t)).re * poissonKernel z t‖ ≤ ‖M * poissonKernel z t‖
    simp only [norm_mul, Real.norm_eq_abs]
    rw [_root_.abs_of_nonneg hk_nonneg, _root_.abs_of_nonneg hM_nonneg]
    exact mul_le_mul_of_nonneg_right (hBound t) hk_nonneg

/-! ## Section 6: Main Existence Results -/

-- (measurability lemmas moved earlier)

/-- Existence of pinch field Poisson representation on off-zeros set -/
theorem pinch_poissonRepOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (hXi : AnalyticOn ℂ riemannXi_ext Ω)
    (hDet_meas : Measurable (fun t => det2 (boundary t)))
    (hO_meas   : Measurable (fun t => O (boundary t)))
    (hXi_meas  : Measurable (fun t => riemannXi_ext (boundary t))) :
    ∀ (hFormula : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch det2 O z).re =
        poissonIntegral (fun t => (F_pinch det2 O (boundary t)).re) z),
    HasPoissonRepOn (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  intro hFormula
  constructor
  · -- subset
    intro z hz
    exact hz.1
  · -- analytic
    exact F_pinch_analyticOn_offZeros hDet2 hO hXi
  · -- integrable
    intro z hz
    have hzΩ : z ∈ Ω := Set.mem_of_mem_diff hz
    apply integrable_boundedBoundary _ _ 2 hzΩ
    · intro t
      exact F_pinch_boundary_bound hBME t
    · -- Measurability of t ↦ (F_pinch det2 O (boundary t)).re
      apply Measurable.comp
      · exact measurable_re
      · exact measurable_boundary_F_pinch hDet_meas hO_meas hXi_meas
  · -- formula
    exact hFormula

-- Note: The classical Poisson identity for the pinch field on the off‑zeros set
-- is provided to this module via callers (see `pinch_hasPoissonRepOn_from_cayley`).

/-- Convenience wrapper (Cayley transport): build a Poisson representation witness for the
pinch field on the off‑zeros set from a supplied half‑plane Poisson real‑part identity on
that set. This avoids any reliance on the axiom `F_pinch_poisson_formula_on_offZeros` by
accepting the identity as an explicit hypothesis. -/
theorem pinch_hasPoissonRepOn_from_cayley
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (hXi : AnalyticOn ℂ riemannXi_ext Ω)
    (hDet_meas : Measurable (fun t : ℝ => det2 (boundary t)))
    (hO_meas   : Measurable (fun t : ℝ => O (boundary t)))
    (hXi_meas  : Measurable (fun t : ℝ => riemannXi_ext (boundary t)))
    (hReEqOn : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
                (F_pinch det2 O z).re =
                  poissonIntegral (fun t : ℝ => (F_pinch det2 O (boundary t)).re) z)
    : HasPoissonRepOn (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- Use the general builder, supplying the real‑part identity as the `hFormula` input.
  refine pinch_poissonRepOn_offZeros hDet2 (hO := hO) (hBME := hBME) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas) ?hFormula
  intro z hz
  exact hReEqOn z hz

/-- Main transport theorem for pinch field -/
theorem pinch_transport
    {O : ℂ → ℂ}
    (hRep : HasPoissonRepOn (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0})) :
    BoundaryPositive (F_pinch det2 O) →
      ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
        0 ≤ (F_pinch det2 O z).re :=
  poissonTransportOn hRep

/-! ## Section 7: Boundary AI Interface (Statement Level) -/

/-- Boundary approximate identity property -/
def BoundaryAI (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ,
    Tendsto (fun b : ℝ => poissonSmooth F b x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (boundaryRe F x))

/-- AI property follows from Poisson representation (statement) -/
def boundaryAI_from_poissonRep (F : ℂ → ℂ) : Prop :=
  HasPoissonRep F → BoundaryAI F
