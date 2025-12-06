import Riemann.RS.Det2Outer

/-!
# Half-plane Outer Functions

This module provides a clean interface for outer functions on the right half-plane
Omega := { s : Complex | Re s > 1/2 }.

It contains: basic definitions (domain/boundary), Poisson kernel and transport,
boundary modulus matching, and pinch field specializations.
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
/-- Off-zeros domain for `riemannXi_ext` on Ω, excluding the pole at `1`. -/
def offXi : Set ℂ := {z | z ∈ Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0}

lemma offXi_subset_Ω : offXi ⊆ Ω := by
  intro z hz
  exact hz.1

lemma offXi_subset_Ω_minus_one : offXi ⊆ Ω \ ({1} : Set ℂ) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hz1
  exact hz.2.1 hz1

lemma boundary_re (t : ℝ) : (boundary t).re = 1/2 := by simp [boundary]

lemma boundary_im (t : ℝ) : (boundary t).im = t := by simp [boundary]

@[simp] lemma boundary_mk_eq (t : ℝ) :
  boundary t = { re := (1/2 : ℝ), im := t } := by
  -- Prove equality by matching real and imaginary parts
  apply Complex.ext
  · simp [boundary]
  · simp [boundary]

/-- Off-zeros inclusion for `offXi` into the larger off-zeros set. -/
lemma offXi_subset_offZeros : offXi ⊆ (Ω \ {z | riemannXi_ext z = 0}) := by
  intro z hz
  refine And.intro hz.1 ?h
  intro h0; exact hz.2.2 (by simpa [Set.mem_setOf_eq] using h0)

/-- An outer function on Ω: analytic and non-vanishing -/
structure IsOuter (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonvanishing : ∀ s ∈ Ω, O s ≠ 0

/-- Boundary modulus equality: |O| = |F| on the critical line -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, norm (O (boundary t)) = norm (F (boundary t))

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
    · exact pow_pos ha 2
    · exact sq_nonneg _
  exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
    (div_nonneg ha.le hdenom.le)

/-! Poisson integral operator (placed before first use) -/

/-- Poisson integral: reconstructs interior values from boundary data -/
@[simp] noncomputable def poissonIntegral (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, u t * poissonKernel z t

/-! ### Kernel bounds and integrability -/

lemma poissonKernel_bound (z : ℂ) (hz : z ∈ Ω) :
    ∃ C > 0, ∀ t : ℝ, ‖poissonKernel z t‖ ≤ C / (1 + (t - z.im)^2) := by
  classical
  -- Set a := Re z − 1/2 > 0 and X := (t − Im z)^2 ≥ 0
  unfold Ω at hz
  simp only [Set.mem_setOf_eq] at hz
  set a : ℝ := z.re - 1/2 with ha_def
  have ha : 0 < a := sub_pos.mpr hz
  -- Define the comparison constant C0 := max(a, 1/a)
  let C0 : ℝ := max a (1 / a)
  -- Core scalar inequality: for all X ≥ 0,
  --   a/(a^2+X) ≤ C0/(1+X)
  have hfrac : ∀ t : ℝ,
      a / (a ^ 2 + (t - z.im) ^ 2) ≤ C0 / (1 + (t - z.im) ^ 2) := by
    intro t
    set X : ℝ := (t - z.im) ^ 2
    have hXnn : 0 ≤ X := by dsimp [X]; exact sq_nonneg _
    have hposA : 0 < a ^ 2 + X := by
      have : 0 < a ^ 2 := by
        have : a ≠ 0 := ne_of_gt ha
        simpa [pow_two] using mul_self_pos.mpr this
      exact add_pos_of_pos_of_nonneg this hXnn
    have hposB : 0 < 1 + X := add_pos_of_pos_of_nonneg (by norm_num) hXnn
    -- Prove a(1+X) ≤ C0(a^2+X), then divide by positives to get the fraction inequality
    have hcore : a * (1 + X) ≤ C0 * (a ^ 2 + X) := by
      have hcases := le_total a (1 : ℝ)
      cases hcases with
      | inl hA_le_one =>
        -- When a ≤ 1, C0 ≥ 1/a and a(1+X) ≤ (1/a)(a^2+X)
        have ha2_le_one : a ^ 2 ≤ (1 : ℝ) := by
          -- since 0 ≤ a and a ≤ 1, we have a^2 ≤ a ≤ 1
          have ha2_le_a : a ^ 2 ≤ a := by
            have := mul_le_mul_of_nonneg_left hA_le_one ha.le
            simpa [pow_two, one_mul] using this
          exact ha2_le_a.trans hA_le_one
        have hX : a ^ 2 * X ≤ X := by
          have := mul_le_mul_of_nonneg_right ha2_le_one hXnn
          simpa using this
        have hx' : a ^ 2 * (1 + X) ≤ a ^ 2 + X := by
          simpa [mul_add] using add_le_add_left hX (a ^ 2)
        have hstep : a * (1 + X) ≤ (1 / a) * (a ^ 2 + X) := by
          -- use le_div_iff₀ with a > 0: (a*(1+X) ≤ (a^2+X)/a) ↔ (a*(1+X))*a ≤ a^2+X
          have hx2 : (a * (1 + X)) * a ≤ a ^ 2 + X := by
            simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hx'
          have hpos : 0 < a := ha
          have h1 : a * (1 + X) ≤ (a ^ 2 + X) / a := (le_div_iff₀ hpos).mpr hx2
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h1
        have hC0_ge : (1 / a) ≤ C0 := by
          dsimp [C0]; exact le_max_right _ _
        have hnonneg : 0 ≤ (a ^ 2 + X) := le_of_lt hposA
        exact le_trans hstep (mul_le_mul_of_nonneg_right hC0_ge hnonneg)
      | inr h_one_le_A =>
        -- When a ≥ 1, C0 ≥ a and a(1+X) ≤ a(a^2+X)
        have h1_le_a2 : (1 : ℝ) ≤ a ^ 2 := by
          -- from 1 ≤ a and a ≥ 0, we get a ≤ a^2, hence 1 ≤ a^2
          have h1_le_a : (1 : ℝ) ≤ a := h_one_le_A
          have ha_nonneg : 0 ≤ a := ha.le
          have h_a_le_a2 : a ≤ a ^ 2 := by
            simpa [pow_two, one_mul] using mul_le_mul_of_nonneg_right h1_le_a ha_nonneg
          exact h1_le_a.trans h_a_le_a2
        have hstep : a * (1 + X) ≤ a * (a ^ 2 + X) := by
          have hx : 1 + X ≤ a ^ 2 + X := add_le_add_right h1_le_a2 X
          exact mul_le_mul_of_nonneg_left hx ha.le
        have hC0_ge : a ≤ C0 := by dsimp [C0]; exact le_max_left _ _
        have hnonneg : 0 ≤ (a ^ 2 + X) := le_of_lt hposA
        exact le_trans hstep (mul_le_mul_of_nonneg_right hC0_ge hnonneg)
    -- Use div/mul monotonicity with positive denominators to conclude the fraction bound
    have hfracX : a / (a ^ 2 + X) ≤ C0 / (1 + X) := by
      -- a*(1+X) ≤ C0*(a^2+X) ⇒ a ≤ (C0*(a^2+X))/(1+X)
      have h1 : a ≤ (C0 * (a ^ 2 + X)) / (1 + X) :=
        (le_div_iff₀ hposB).2 hcore
      -- rewrite to (C0/(1+X)) * (a^2+X)
      have h1' : a ≤ (C0 / (1 + X)) * (a ^ 2 + X) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h1
      -- divide by (a^2+X)>0 on the left
      exact (div_le_iff₀ hposA).2 h1'
    simpa [X] using hfracX
  -- Multiply by 1/π
  have hπpos : 0 < (1 / Real.pi) := one_div_pos.mpr Real.pi_pos
  refine ⟨(1 / Real.pi) * C0, ?Cpos, ?bound⟩
  ·
    have hC0pos : 0 < C0 := by
      dsimp [C0]
      exact lt_of_lt_of_le ha (le_max_left _ _)
    exact mul_pos hπpos hC0pos
  · intro t
    have hscaled : (1 / Real.pi) * (a / (a ^ 2 + (t - z.im) ^ 2))
        ≤ (1 / Real.pi) * (C0 / (1 + (t - z.im) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hfrac t) (le_of_lt hπpos)
    have hval_flat : (1 / Real.pi) * (a / (a ^ 2 + (t - z.im) ^ 2))
        ≤ 1 / Real.pi * C0 / (1 + (t - z.im) ^ 2) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hscaled
    have hval : poissonKernel z t ≤ 1 / Real.pi * C0 / (1 + (t - z.im) ^ 2) := by
      simpa [poissonKernel, ha_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hval_flat
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    have : ‖poissonKernel z t‖ ≤ 1 / Real.pi * C0 / (1 + (t - z.im) ^ 2) := by
      rw [Real.norm_eq_abs, _root_.abs_of_nonneg hk_nonneg]
      exact hval
    exact this

/-- Integrability of the Poisson kernel for `z ∈ Ω`. -/
lemma poissonKernel_integrable {z : ℂ} (hz : z ∈ Ω) :
    Integrable (fun t => poissonKernel z t) := by
  -- Use the bound by a multiple of 1/(1+(t-b)²) and its known integrability
  obtain ⟨C, hCpos, hbound⟩ := poissonKernel_bound z hz
  -- 1/(1+(t-b)^2) is integrable (shift of the standard integrable kernel)
  have : Integrable (fun t : ℝ => 1 / (1 + (t - z.im) ^ 2)) := by
    simpa [sub_eq_add_neg, pow_two] using (integrable_inv_one_add_sq.comp_sub_right z.im)
  have hint : Integrable (fun t : ℝ => C / (1 + (t - z.im) ^ 2)) := by
    simpa [div_eq_mul_inv] using this.const_mul C
  -- Comparison using strong measurability (dominate by the scalar bound)
  refine hint.mono ?meas ?bound
  · -- measurability
    -- kernel is continuous hence measurable
    apply Continuous.aestronglyMeasurable
    unfold poissonKernel
    apply Continuous.mul
    · exact continuous_const
    · apply Continuous.div
      · exact continuous_const
      · apply Continuous.add
        · exact continuous_const
        · apply Continuous.pow
          exact (continuous_id.sub continuous_const)
      · intro t; apply ne_of_gt; apply add_pos_of_pos_of_nonneg
        ·
          have hzlt : (1/2 : ℝ) < z.re := by
            simpa [Ω, Set.mem_setOf_eq] using hz
          have : 0 < z.re - 1/2 := sub_pos.mpr hzlt
          exact pow_pos this 2
        · exact sq_nonneg _
  · -- pointwise bound to feed domination: ‖kernel‖ ≤ C/(1+(t-b)^2)
    filter_upwards with t
    -- Normalize the RHS to the scalar flattening used in the bound above
    have hb := hbound t
    have hC_pos : 0 ≤ C := le_of_lt hCpos
    have hden_pos : 0 < 1 + (t - z.im) ^ 2 := by
      apply add_pos_of_pos_of_nonneg; norm_num; exact sq_nonneg _
    have hdiv_nonneg : 0 ≤ C / (1 + (t - z.im) ^ 2) := div_nonneg hC_pos (le_of_lt hden_pos)
    have : ‖C / (1 + (t - z.im) ^ 2)‖ = C / (1 + (t - z.im) ^ 2) := by
      rw [Real.norm_eq_abs, _root_.abs_of_nonneg hdiv_nonneg]
    rw [this]
    exact hb

/-- If a real function `u` on the boundary is bounded by `M`, then
its product with the Poisson kernel is integrable. -/
lemma integrable_boundedBoundary
    (u : ℝ → ℝ) (z : ℂ) (M : ℝ)
    (hz : z ∈ Ω)
    (hBound : ∀ t : ℝ, |u t| ≤ M)
    (hMeas : Measurable u) :
    Integrable (fun t => u t * poissonKernel z t) := by
  -- Kernel integrable
  have hker : Integrable (fun t => poissonKernel z t) := poissonKernel_integrable hz
  -- Dominating integrable function: max M 0 · kernel (nonnegative coefficient)
  have hDom : Integrable (fun t => (‖max M 0‖) * poissonKernel z t) :=
    Integrable.const_mul hker (‖max M 0‖)
  -- Strong measurability of kernel via continuity
  have hker_meas : AEStronglyMeasurable (fun t => poissonKernel z t) := by
    refine (Continuous.aestronglyMeasurable ?_)
    unfold poissonKernel
    apply Continuous.mul
    · exact continuous_const
    · apply Continuous.div
      · exact continuous_const
      · apply Continuous.add
        · exact continuous_const
        · apply Continuous.pow
          exact (continuous_id.sub continuous_const)
      · intro t; apply ne_of_gt; apply add_pos_of_pos_of_nonneg
        · have : 0 < z.re - 1/2 := sub_pos.mpr hz; exact pow_pos this 2
        · exact sq_nonneg _
  -- Apply domination by max M 0 * kernel
  refine hDom.mono (hMeas.aestronglyMeasurable.mul hker_meas) ?_
  filter_upwards with t
  have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
  have habs_le : |u t| ≤ max M 0 := le_trans (hBound t) (le_max_left _ _)
  have hcoef : ‖u t‖ ≤ ‖max M 0‖ := by
    have hbase : ‖u t‖ ≤ max M 0 := by
      calc
        ‖u t‖ = |u t| := by simp [Real.norm_eq_abs]
        _ ≤ max M 0 := habs_le
    have h0 : 0 ≤ max M 0 :=
      le_max_of_le_right (show 0 ≤ (0 : ℝ) from le_rfl)
    have hnorm_max : ‖max M 0‖ = max M 0 := by
      simp [Real.norm_eq_abs, _root_.abs_of_nonneg h0]
    have hrew : max M 0 = ‖max M 0‖ := by simp [hnorm_max]
    exact hrew ▸ hbase
  have : ‖u t * poissonKernel z t‖ ≤ ‖(‖max M 0‖) * poissonKernel z t‖ := by
    have : ‖u t‖ ≤ ‖max M 0‖ := hcoef
    have hmul : ‖u t‖ * ‖poissonKernel z t‖ ≤ ‖max M 0‖ * ‖poissonKernel z t‖ :=
      mul_le_mul_of_nonneg_right this (norm_nonneg _)
    simpa [norm_mul, Real.norm_eq_abs, _root_.abs_of_nonneg hk_nonneg,
           mul_comm, mul_left_comm, mul_assoc] using hmul
  exact this

/-! ### Measurability helpers (placed early to be available downstream) -/

lemma measurable_boundary_affine : Measurable (boundary : ℝ → ℂ) := by
  unfold boundary
  apply Measurable.add
  · exact measurable_const
  · apply Measurable.const_mul
    exact Complex.continuous_ofReal.measurable

/-- Pullback measurability along the AF boundary map. -/
lemma measurable_on_boundary_of_measurable {α} [MeasurableSpace α]
  {f : ℂ → α} (hf : Measurable f) :
  Measurable (fun t : ℝ => f (boundary t)) :=
  hf.comp measurable_boundary_affine

/-- Alias with argument order matching RS callers. -/
lemma measurable_comp_boundary {α} [MeasurableSpace α]
  (f : ℂ → α) (hf : Measurable f) :
  Measurable (fun t : ℝ => f (boundary t)) :=
  measurable_on_boundary_of_measurable (f := f) hf

lemma xi_ext_boundary_measurable :
  Measurable (fun t : ℝ => riemannXi_ext (boundary t)) :=
  measurable_comp_boundary (f := riemannXi_ext)
    RH.AcademicFramework.CompletedXi.measurable_riemannXi_ext

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

/-! ### Pinch field primitives (defined here to avoid RS↔AF cycles) -/

/-- Paper choice: define `J_pinch := det₂ / (O · ξ_ext)` on Ω. -/
noncomputable def J_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun s => det2 s / (O s * riemannXi_ext s)

/-- The pinch field `F := 2 · J_pinch det2 O`. -/
@[simp] noncomputable def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ) * J_pinch det2 O z

/-! ### Analyticity of pinch field on offXi -/

/-- Analyticity of `J_pinch` on the AF off-zeros set `offXi`. -/
lemma J_pinch_analyticOn_offXi
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (J_pinch det2 O) offXi := by
  -- Work on S = offXi ⊆ Ω and S ⊆ Ω\{1}
  let S : Set ℂ := offXi
  have hSsubΩ : S ⊆ Ω := offXi_subset_Ω
  have hSsubΩm1 : S ⊆ Ω \ ({1} : Set ℂ) := offXi_subset_Ω_minus_one
  -- Restrict analyticity of factors
  have hDet2_S : AnalyticOn ℂ det2 S := (hDet2.analytic.mono hSsubΩ)
  have hO_S    : AnalyticOn ℂ O S    := (hO.analytic.mono hSsubΩ)
  have hXi_S   : AnalyticOn ℂ riemannXi_ext S := (hXi.mono hSsubΩm1)
  -- Denominator nonzero on S: O is nonzero on Ω and ξ_ext ≠ 0 on offXi
  have hDen_ne : ∀ z ∈ S, (O z * riemannXi_ext z) ≠ 0 := by
    intro z hz
    have hzΩ : z ∈ Ω := hSsubΩ hz
    have hOnz : O z ≠ 0 := hO.nonzero hzΩ
    have hXinz : riemannXi_ext z ≠ 0 := hz.2.2
    exact mul_ne_zero hOnz hXinz
  -- Assemble division analytic on S
  have hProd : AnalyticOn ℂ (fun z => O z * riemannXi_ext z) S := by
    simpa using hO_S.mul hXi_S
  have hInv : AnalyticOn ℂ (fun z => (O z * riemannXi_ext z)⁻¹) S :=
    AnalyticOn.inv hProd hDen_ne
  have hQuot : AnalyticOn ℂ (fun z => det2 z * (O z * riemannXi_ext z)⁻¹) S := by
    simpa using hDet2_S.mul hInv
  refine (hQuot.congr ?_)
  intro z _; simp [J_pinch, div_eq_mul_inv]

/-- Analyticity of `F_pinch` on `offXi`. -/
lemma F_pinch_analyticOn_offXi
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (F_pinch det2 O) offXi := by
  -- F_pinch = 2 * J_pinch on S := offXi
  have hJ := J_pinch_analyticOn_offXi hDet2 hO hXi
  have h2 : AnalyticOn ℂ (fun _ => (2 : ℂ)) offXi := analyticOn_const
  simpa [F_pinch] using h2.mul hJ

/-- Analyticity of `J_pinch` on `offXi` assuming only analyticity of `det2` on `Ω`. -/
lemma J_pinch_analyticOn_offXi_of_analytic
    (hDet2A : AnalyticOn ℂ det2 Ω)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (J_pinch det2 O) offXi := by
  -- Work on S = offXi ⊆ Ω and S ⊆ Ω\{1}
  let S : Set ℂ := offXi
  have hSsubΩ : S ⊆ Ω := offXi_subset_Ω
  have hSsubΩm1 : S ⊆ Ω \ ({1} : Set ℂ) := offXi_subset_Ω_minus_one
  -- Restrict analyticity of factors
  have hDet2_S : AnalyticOn ℂ det2 S := (hDet2A.mono hSsubΩ)
  have hO_S    : AnalyticOn ℂ O S    := (hO.analytic.mono hSsubΩ)
  have hXi_S   : AnalyticOn ℂ riemannXi_ext S := (hXi.mono hSsubΩm1)
  -- Denominator nonzero on S: O is nonzero on Ω and ξ_ext ≠ 0 on offXi
  have hDen_ne : ∀ z ∈ S, (O z * riemannXi_ext z) ≠ 0 := by
    intro z hz
    have hzΩ : z ∈ Ω := hSsubΩ hz
    have hOnz : O z ≠ 0 := hO.nonzero hzΩ
    have hXinz : riemannXi_ext z ≠ 0 := hz.2.2
    exact mul_ne_zero hOnz hXinz
  -- Assemble division analytic on S
  have hProd : AnalyticOn ℂ (fun z => O z * riemannXi_ext z) S := by
    simpa using hO_S.mul hXi_S
  have hInv : AnalyticOn ℂ (fun z => (O z * riemannXi_ext z)⁻¹) S :=
    AnalyticOn.inv hProd hDen_ne
  have hQuot : AnalyticOn ℂ (fun z => det2 z * (O z * riemannXi_ext z)⁻¹) S := by
    simpa using hDet2_S.mul hInv
  refine (hQuot.congr ?_)
  intro z _; simp [J_pinch, div_eq_mul_inv]

/-- Analyticity of `F_pinch` on `offXi` assuming only analyticity of `det2` on `Ω`. -/
lemma F_pinch_analyticOn_offXi_of_analytic
    (hDet2A : AnalyticOn ℂ det2 Ω)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (F_pinch det2 O) offXi := by
  have hJ := J_pinch_analyticOn_offXi_of_analytic hDet2A hO hXi
  have h2 : AnalyticOn ℂ (fun _ => (2 : ℂ)) offXi := analyticOn_const
  simpa [F_pinch] using h2.mul hJ

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

/-- Restrict a global half‑plane Poisson representation to any subset `S ⊆ Ω`. -/
theorem repOn_of_rep_subset {F : ℂ → ℂ} {S : Set ℂ}
  (hRep : HasPoissonRep F) (hS : S ⊆ Ω) : HasPoissonRepOn F S := by
  refine {
    subset := hS
    , analytic := ?hA
    , integrable := ?hI
    , formula := ?hEq }
  · -- analytic on S by restriction
    exact hRep.analytic.mono hS
  · -- integrable on S by restriction
    intro z hzS
    exact hRep.integrable z (hS hzS)
  · -- Poisson real‑part identity on S by restriction
    intro z hzS
    exact hRep.formula z (hS hzS)

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

-- legacy off-zeros variant retained for callers still using the older set
lemma J_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (J_pinch det2 O) offXi := by
  exact J_pinch_analyticOn_offXi hDet2 hO hXi

/-- Analyticity of F_pinch on the off-zeros set -/
lemma F_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (F_pinch det2 O) offXi := by
  exact F_pinch_analyticOn_offXi hDet2 hO hXi

/-! ### Boundary absolute-value control for the pinch field -/

lemma boundary_abs_J_pinch_eq_one
  {O : ℂ → ℂ}
  (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (t : ℝ)
  (hO : O (boundary t) ≠ 0)
  (hXi : riemannXi_ext (boundary t) ≠ 0) :
  norm (J_pinch det2 O (boundary t)) = 1 := by
  classical
  -- abbreviate z := boundary t
  set z : ℂ := boundary t
  have hOabs : norm (O z) = norm (det2 z / riemannXi_ext z) := by
    simpa [z] using hBME t
  have hO0  : O z ≠ 0 := by simpa [z] using hO
  have hXi0 : riemannXi_ext z ≠ 0 := by simpa [z] using hXi
  -- |O|·|ξ| = |det2|
  have hprod : norm (O z) * norm (riemannXi_ext z) = norm (det2 z) := by
    calc
      norm (O z) * norm (riemannXi_ext z)
          = norm (det2 z / riemannXi_ext z) * norm (riemannXi_ext z) := by
                simp [hOabs]
      _ = norm ((det2 z / riemannXi_ext z) * (riemannXi_ext z)) :=
        (Complex.norm_mul (det2 z / riemannXi_ext z) (riemannXi_ext z)).symm
      _ = norm (det2 z) := by
        have hxinv : (riemannXi_ext z)⁻¹ * (riemannXi_ext z) = (1 : ℂ) := inv_mul_cancel₀ hXi0
        calc
          norm ((det2 z / riemannXi_ext z) * (riemannXi_ext z))
              = norm (det2 z * ((riemannXi_ext z)⁻¹ * (riemannXi_ext z))) := by
                    simp [div_eq_mul_inv, mul_comm, mul_assoc]
      _ = norm (det2 z * 1) := by
        simp [hxinv]
          _ = norm (det2 z) := by simp
  -- |J| = |det2| / (|O|·|ξ|) = 1
  have hden_pos : 0 < norm (O z) * norm (riemannXi_ext z) := by
    have h1 : 0 < norm (O z) := by exact norm_pos_iff.mpr hO
    have h2 : 0 < norm (riemannXi_ext z) := by exact norm_pos_iff.mpr hXi
    exact mul_pos h1 h2
  have hden_ne : norm (O z) * norm (riemannXi_ext z) ≠ 0 :=
    ne_of_gt hden_pos
  have hJabs : norm (J_pinch det2 O z)
      = norm (det2 z) / (norm (O z) * norm (riemannXi_ext z)) := by
    calc
      norm (J_pinch det2 O z)
          = norm (det2 z / (O z * riemannXi_ext z)) := by
              simp [J_pinch]
      _ = norm (det2 z) / norm (O z * riemannXi_ext z) := by
              simp
      _ = norm (det2 z) / (norm (O z) * norm (riemannXi_ext z)) := by
              simp
  have hratio : norm (J_pinch det2 O z)
      = norm (det2 z) / (norm (O z) * norm (riemannXi_ext z)) := hJabs
  have hJ_abs_det2 : norm (J_pinch det2 O z) = 1 := by
    -- |det2| / (|O|·|ξ|) = 1 from boundary modulus
    have : norm (det2 z)
        = norm (O z) * norm (riemannXi_ext z) := by
      exact hprod.symm
    rw [hratio, this, div_self hden_ne]
  show norm (J_pinch det2 O (boundary t)) = 1
  exact hJ_abs_det2

/-- Uniform boundary bound for the real part of the pinch field:
`|(F_pinch det2 O (boundary t)).re| ≤ 2` for all real `t`. -/
lemma F_pinch_boundary_bound
  {O : ℂ → ℂ}
  (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (t : ℝ) :
  |((F_pinch det2 O) (boundary t)).re| ≤ (2 : ℝ) := by
  classical
  set z : ℂ := boundary t
  -- Either the denominator vanishes or not; in both cases `|J| ≤ 1`.
  have hJ_le_one : norm (J_pinch det2 O z) ≤ 1 := by
    by_cases hO0 : O z = 0
    · -- denominator zero ⇒ J = 0
      have hJ0 : J_pinch det2 O z = 0 := by simp [J_pinch, hO0]
      -- |J| ≤ 1 holds since |0| ≤ 1
      rw [hJ0]; rw [norm_zero] -- Complex.abs.map_zero]
      norm_num
    · by_cases hXi0 : riemannXi_ext z = 0
      · have hJ0 : J_pinch det2 O z = 0 := by simp [J_pinch, hXi0]
        rw [hJ0,norm_zero]
        norm_num
      · -- nonzero denominator: unit modulus on the boundary
        have hO_ne : O (boundary t) ≠ 0 := by show O z ≠ 0; exact hO0
        have hXi_ne : riemannXi_ext (boundary t) ≠ 0 := by show riemannXi_ext z ≠ 0; exact hXi0
        have hEq : norm (J_pinch det2 O z) = 1 :=
          boundary_abs_J_pinch_eq_one (O := O) hBME t hO_ne hXi_ne
        -- Align with the simp-normal form where det₂ is rewritten to det2_AF
        -- finalize ≤ 1
        rw [hEq]
  -- |Re(2·J)| ≤ |2·J| = 2·|J| ≤ 2
  have hRe_le_abs : |((F_pinch det2 O) z).re| ≤ norm ((F_pinch det2 O) z) := by
    simpa using (Complex.abs_re_le_norm ((F_pinch det2 O) z))
  have hAbs_F : norm ((F_pinch det2 O) z) = (2 : ℝ) * norm (J_pinch det2 O z) := by
    simp [F_pinch]
  have : |((F_pinch det2 O) z).re| ≤ (2 : ℝ) * norm (J_pinch det2 O z) := by
    simpa [hAbs_F] using hRe_le_abs
  have : |((F_pinch det2 O) z).re| ≤ (2 : ℝ) * 1 :=
    (le_trans this (mul_le_mul_of_nonneg_left hJ_le_one (by norm_num)))
  simpa [z] using this

/-! ## Measurability of boundary trace for the pinch field -/

lemma measurable_boundary_F_pinch
    {O : ℂ → ℂ}
    (hDet_meas : Measurable (fun t : ℝ => det2 (boundary t)))
    (hO_meas   : Measurable (fun t : ℝ => O (boundary t)))
    (hXi_meas  : Measurable (fun t : ℝ => riemannXi_ext (boundary t))) :
    Measurable (fun t : ℝ => (F_pinch det2 O (boundary t)).re) := by
  -- F_pinch = 2 * (det2 / (O * ξ))
  have hJ_meas : Measurable (fun t : ℝ => J_pinch det2 O (boundary t)) := by
    -- Build measurability via algebraic composition rules
    have hden_meas : Measurable (fun t : ℝ => O (boundary t) * riemannXi_ext (boundary t)) := by
      exact hO_meas.mul hXi_meas
    have hden_inv_meas : Measurable (fun t : ℝ => (O (boundary t) * riemannXi_ext (boundary t))⁻¹) :=
      hden_meas.inv
    have hnum_meas : Measurable (fun t : ℝ => det2 (boundary t)) := hDet_meas
    simpa [J_pinch, div_eq_mul_inv] using hnum_meas.mul hden_inv_meas
  -- Multiply by 2 and take real part
  have hF_meas : Measurable (fun t : ℝ => (F_pinch det2 O (boundary t))) := by
    simpa [F_pinch] using (measurable_const.mul hJ_meas)
  exact measurable_re.comp hF_meas

/-! ## Section 6: Main Existence Results -/

-- (measurability lemmas moved earlier)

/-- Existence of pinch field Poisson representation on off-zeros set -/
theorem pinch_poissonRepOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)))
    (hDet_meas : Measurable (fun t => det2 (boundary t)))
    (hO_meas   : Measurable (fun t => O (boundary t)))
    (hXi_meas  : Measurable (fun t => riemannXi_ext (boundary t))) :
    (∀ z ∈ offXi,
      (F_pinch det2 O z).re =
        poissonIntegral (fun t => (F_pinch det2 O (boundary t)).re) z) →
    HasPoissonRepOn (F_pinch det2 O) offXi := by
  intro hFormula
  constructor
  · -- subset
    exact offXi_subset_Ω
  · -- analytic on offXi
    exact F_pinch_analyticOn_offXi hDet2 hO hXi
  · -- integrable
    intro z hz
    have hzΩ : z ∈ Ω := offXi_subset_Ω hz
    have hBound : ∀ t : ℝ, |((F_pinch det2 O) (boundary t)).re| ≤ (2 : ℝ) :=
      fun t => F_pinch_boundary_bound (O := O) hBME t
    have hMeas : Measurable (fun t => ((F_pinch det2 O) (boundary t)).re) :=
      measurable_boundary_F_pinch hDet_meas hO_meas hXi_meas
    simpa using integrable_boundedBoundary
      (u := fun t : ℝ => ((F_pinch det2 O) (boundary t)).re)
      (z := z) (M := (2 : ℝ)) hzΩ hBound hMeas
  · -- formula on offXi: supplied as hypothesis
    intro z hz
    exact hFormula z hz

/-- Convenience wrapper (Cayley transport): build a Poisson representation witness for the
pinch field on the off‑zeros set from a supplied half‑plane Poisson real‑part identity on
that set. This avoids any reliance on the axiom `F_pinch_poisson_formula_on_offZeros` by
accepting the identity as an explicit hypothesis. -/
theorem pinch_hasPoissonRepOn_from_cayley
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)))
    (hDet_meas : Measurable (fun t => det2 (boundary t)))
    (hO_meas   : Measurable (fun t => O (boundary t)))
    (hXi_meas  : Measurable (fun t => riemannXi_ext (boundary t)))
    (hReEqOn : ∀ z ∈ offXi,
                (F_pinch det2 O z).re =
                  poissonIntegral (fun t : ℝ => (F_pinch det2 O (boundary t)).re) z)
    : HasPoissonRepOn (F_pinch det2 O) offXi := by
  -- Use the general builder, supplying the real‑part identity as the `hFormula` input.
  exact pinch_poissonRepOn_offZeros hDet2 (hO := hO) (hBME := hBME) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas) hReEqOn

/-
Convenience wrapper (Cayley transport, analytic-only det₂): build a Poisson
representation witness for the pinch field on the off-zeros set assuming only
`AnalyticOn det2 Ω` (no det₂ nonvanishing assumed).
-/
theorem pinch_hasPoissonRepOn_from_cayley_analytic
    (hDet2A : AnalyticOn ℂ det2 Ω)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)))
    (hDet_meas : Measurable (fun t => det2 (boundary t)))
    (hO_meas   : Measurable (fun t => O (boundary t)))
    (hXi_meas  : Measurable (fun t => riemannXi_ext (boundary t)))
    (hReEqOn : ∀ z ∈ offXi,
                (F_pinch det2 O z).re =
                  poissonIntegral (fun t : ℝ => (F_pinch det2 O (boundary t)).re) z)
    : HasPoissonRepOn (F_pinch det2 O) offXi := by
  constructor
  · -- subset
    exact offXi_subset_Ω
  · -- analytic on offXi (via analytic-only variant)
    exact F_pinch_analyticOn_offXi_of_analytic hDet2A hO hXi
  · -- integrable (same proof as non-analytic builder)
    intro z hz
    have hzΩ : z ∈ Ω := offXi_subset_Ω hz
    have hBound : ∀ t : ℝ, |((F_pinch det2 O) (boundary t)).re| ≤ (2 : ℝ) :=
      fun t => F_pinch_boundary_bound (O := O) hBME t
    have hMeas : Measurable (fun t => ((F_pinch det2 O) (boundary t)).re) :=
      measurable_boundary_F_pinch hDet_meas hO_meas hXi_meas
    simpa using integrable_boundedBoundary
      (u := fun t : ℝ => ((F_pinch det2 O) (boundary t)).re)
      (z := z) (M := (2 : ℝ)) hzΩ hBound hMeas

  · -- formula
    exact hReEqOn

/-- Main transport theorem for pinch field -/
theorem pinch_transport
    {O : ℂ → ℂ}
    (hRep : HasPoissonRepOn (F_pinch det2 O) offXi) :
    BoundaryPositive (F_pinch det2 O) →
      ∀ z ∈ offXi,
        0 ≤ (F_pinch det2 O z).re :=
  poissonTransportOn hRep

/-! ## Section 7: Boundary AI Interface (Statement Level) -/

/-- Boundary real trace for `F` along the canonical parameterisation. -/
@[simp] noncomputable def boundaryRe (F : ℂ → ℂ) (x : ℝ) : ℝ :=
  (F (boundary x)).re

/-- Poisson smoothing family on the boundary; used to state the AI property. -/
@[simp] noncomputable def poissonSmooth (F : ℂ → ℂ) (b x : ℝ) : ℝ :=
  ∫ t : ℝ,
    (b / (Real.pi * (b^2 + (x - t)^2))) * boundaryRe F t

/-- Boundary approximate identity property -/
def BoundaryAI (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ,
    Tendsto (fun b : ℝ => poissonSmooth F b x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (boundaryRe F x))

/-- AI property follows from Poisson representation (statement) -/
def boundaryAI_from_poissonRep (F : ℂ → ℂ) : Prop :=
  HasPoissonRep F → BoundaryAI F
