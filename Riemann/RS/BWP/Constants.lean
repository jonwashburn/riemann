import Riemann.Mathlib.ArctanTwoGtOnePointOne
import Riemann.RS.CRGreenOuter
import Riemann.RS.WhitneyAeCore

/-!
# Boundary Wedge Constants and Upsilon Computation

This module defines the key constants used in the boundary wedge proof and proves
that the wedge parameter Υ < 1/2, which is the core RH-specific arithmetic.

## Main Contents

1. **PPlus Definitions** - Boundary positivity predicate
2. **Paper Constants** - c₀, K₀, Kξ, C_ψ from the paper
3. **Upsilon Computation** - Proof that Υ < 1/2 (key RH result)
4. **Parameterized Bounds** - General Υ(Kξ) < 1/2 conditions

The key result is `upsilon_less_than_half : Upsilon_paper < 1/2`, which shows
that the constants from the paper satisfy the wedge closure condition.
-/

namespace Real

open Set

lemma tan_strictMono_mono {s : Set ℝ}
  (hs : s ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
  StrictMonoOn Real.tan s := by
  intro x hx y hy hxy
  exact Real.strictMonoOn_tan (hs hx) (hs hy) hxy

end Real

namespace RH.RS.BoundaryWedgeProof

open Real Complex
open RH.RS.WhitneyAeCore
--open RH.Cert.KxiWhitneyRvM

/-! ## Preliminary Bounds on arctan and pi -/


theorem arctan_two_gt_one_point_one : (1.1 : ℝ) < Real.arctan 2 := by
  -- reuse the global Real-level theorem
  simpa using Real.arctan_two_gt_one_point_one


/-- Standard: arctan is bounded by pi/2. -/
theorem arctan_le_pi_div_two : ∀ x : ℝ, Real.arctan x ≤ Real.pi / 2 := by
  intro x
  exact le_of_lt (Real.arctan_lt_pi_div_two x)

/-- Standard numerical bound: pi > 3.14. -/
theorem pi_gt_314 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2

/-! ## Section 1: Boundary Wedge Predicate -/

/-- Boundary wedge (P+): Re F(1/2+it) ≥ 0 a.e. for F = 2·J_CR.
This is the key boundary positivity that gets transported to the interior. -/
def PPlus_holds (O : OuterOnOmega) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((2 : ℂ) * J_CR O (boundary t)).re

/-- Alias using the canonical outer from ACTION 2. -/
def PPlus_canonical : Prop := PPlus_holds outer_exists

/-- Convenience: identify the BoundaryWedge `(P+)` predicate with the core
`WhitneyAeCore.PPlus_canonical` used in the AF/Route B wiring. Since both
definitions expand to the same a.e. inequality for `2 · J_CR outer_exists`
along the canonical boundary parametrisation, this is by definitional
equality. -/
lemma PPlus_canonical_iff_core :
  PPlus_canonical ↔ WhitneyAeCore.PPlus_canonical := Iff.rfl

lemma PPlus_canonical_to_core :
  PPlus_canonical → WhitneyAeCore.PPlus_canonical := by
  intro h; exact h

lemma PPlus_canonical_of_core :
  WhitneyAeCore.PPlus_canonical → PPlus_canonical := by
  intro h; exact h

/-! ## Section 2: Paper Constants

These are the locked constants from your paper (Section "PSC certificate").
We bind `c0_paper` directly to its closed form to avoid importing modules with
placeholders on the active proof path.
-/

/-- c₀(ψ) = (1/2pi)·arctan(2) ≈ 0.17620819 (classical closed form) -/
noncomputable def c0_paper : ℝ := (Real.arctan (2 : ℝ)) / (2 * Real.pi)

/-- Positivity of c₀(ψ). -/
lemma c0_positive : 0 < c0_paper := by
  have hatan_pos : 0 < Real.arctan (2 : ℝ) := by
    have hmono : StrictMono Real.arctan := Real.arctan_strictMono
    have : Real.arctan 0 < Real.arctan 2 := hmono (by norm_num)
    simp
  have hden_pos : 0 < 2 * Real.pi := by
    have : (0 : ℝ) < 2 := by norm_num
    exact mul_pos this Real.pi_pos
  exact div_pos hatan_pos hden_pos

/-- K₀ = 0.03486808 (arithmetic tail constant from paper) -/
noncomputable def K0_paper : ℝ := 0.03486808

/-- Kξ ≈ 0.16 (Whitney energy from VK zero-density, from paper).
This is an UNCONDITIONAL bound from Vinogradov-Korobov zero-density estimates.
VK bounds are proven unconditionally (not assuming RH). -/
noncomputable def Kxi_paper : ℝ := 0.16

/-- C_ψ^(H¹) = 0.24 (window constant from paper) -/
noncomputable def C_psi_H1 : ℝ := 0.24

/-- Box constant: C_box = K₀ + Kξ -/
noncomputable def C_box_paper : ℝ := K0_paper + Kxi_paper

lemma sqrt_K0_add_Kxi_le :
    Real.sqrt (K0_paper + Kxi_paper) ≤ (447 : ℝ) / 1000 := by
  have h_nonneg : 0 ≤ (447 : ℝ) / 1000 := by norm_num
  have h_sq : (K0_paper + Kxi_paper) ≤ ((447 : ℝ) / 1000) ^ 2 := by
    have h_sum : K0_paper + Kxi_paper = 0.19486808 := by
      norm_num [K0_paper, Kxi_paper]
    have h_pow : ((447 : ℝ) / 1000) ^ 2 = 0.199809 := by
      norm_num
    have : (0.19486808 : ℝ) ≤ 0.199809 := by norm_num
    simpa [h_sum, h_pow] using this
  exact (Real.sqrt_le_iff).mpr ⟨h_nonneg, h_sq⟩

lemma four_Cpsi_mul_sqrt_le :
    (4 * C_psi_H1) * Real.sqrt (K0_paper + Kxi_paper)
      ≤ (10728 : ℝ) / 25000 := by
  have h_nonneg : 0 ≤ (4 : ℝ) * C_psi_H1 := by
    norm_num [C_psi_H1]
  have h := mul_le_mul_of_nonneg_left sqrt_K0_add_Kxi_le h_nonneg
  have h_eval :
      (4 * C_psi_H1) * ((447 : ℝ) / 1000) = (10728 : ℝ) / 25000 := by
    norm_num [C_psi_H1]
  simpa [h_eval]
    using h

lemma four_Cpsi_mul_sqrt_lt :
    (4 * C_psi_H1) * Real.sqrt (K0_paper + Kxi_paper)
      < (2 : ℝ)⁻¹ * Real.arctan 2 := by
  have h_le := four_Cpsi_mul_sqrt_le
  have h_step : (10728 : ℝ) / 25000 < (11 : ℝ) / 20 := by
    norm_num
  have h_arctan_lower : (11 : ℝ) / 10 < Real.arctan 2 := by
    simpa [show (1.1 : ℝ) = (11 : ℝ) / 10 by norm_num]
      using arctan_two_gt_one_point_one
  have h_half_pos : (0 : ℝ) < (2 : ℝ)⁻¹ := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact inv_pos.mpr this
  have h_half : (11 : ℝ) / 20 < (2 : ℝ)⁻¹ * Real.arctan 2 := by
    have h_mul := mul_lt_mul_of_pos_left h_arctan_lower h_half_pos
    have h_left : (2 : ℝ)⁻¹ * ((11 : ℝ) / 10) = (11 : ℝ) / 20 := by
      norm_num
    simpa [h_left]
      using h_mul
  have h_bound : (10728 : ℝ) / 25000 < (2 : ℝ)⁻¹ * Real.arctan 2 :=
    lt_trans h_step h_half
  exact lt_of_le_of_lt h_le h_bound

-- Helper lemma: Algebraic identity for Υ computation (pure arithmetic)
-- This is verifiable by computer algebra, but tactics struggle with nested divisions
lemma upsilon_ratio_eq :
  ((2 / Real.pi) * ((4 / Real.pi) * C_psi_H1 *
      Real.sqrt (K0_paper + Kxi_paper))) /
      ((Real.arctan 2) / (2 * Real.pi))
    = (16 * C_psi_H1 * Real.sqrt (K0_paper + Kxi_paper)) /
      (Real.pi * Real.arctan 2) := by
  set B := C_psi_H1 * Real.sqrt (K0_paper + Kxi_paper) with hB
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hatan_pos : 0 < Real.arctan (2 : ℝ) := by
    have hmono : StrictMono Real.arctan := Real.arctan_strictMono
    have : Real.arctan 0 < Real.arctan 2 := hmono (by norm_num)
    simp
  have hatan_ne : Real.arctan (2 : ℝ) ≠ 0 := ne_of_gt hatan_pos
  have hmain :
      ((2 / Real.pi) * (4 / Real.pi)) /
          ((Real.arctan 2) / (2 * Real.pi))
        = (16 : ℝ) / (Real.pi * Real.arctan 2) := by
    field_simp [hpi_ne, hatan_ne, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hden_ne : (Real.arctan 2) / (2 * Real.pi) ≠ 0 := by
    refine div_ne_zero hatan_ne ?_
    simp
  have hEq :
      ((2 / Real.pi) * ((4 / Real.pi) * B)) /
          ((Real.arctan 2) / (2 * Real.pi))
        = (16 * B) / (Real.pi * Real.arctan 2) := by
    calc
      ((2 / Real.pi) * ((4 / Real.pi) * B)) /
            ((Real.arctan 2) / (2 * Real.pi))
          = (((2 / Real.pi) * (4 / Real.pi)) * B) /
              ((Real.arctan 2) / (2 * Real.pi)) := by
                simp [mul_comm, mul_assoc]
      _ = (B * ((2 / Real.pi) * (4 / Real.pi))) /
              ((Real.arctan 2) / (2 * Real.pi)) := by
                ring_nf
      _ = B * (((2 / Real.pi) * (4 / Real.pi)) /
              ((Real.arctan 2) / (2 * Real.pi))) := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using (mul_div_assoc B ((2 / Real.pi) * (4 / Real.pi))
                      ((Real.arctan 2) / (2 * Real.pi)))
      _ = B * ((16 : ℝ) / (Real.pi * Real.arctan 2)) := by
                simp [hmain]
      _ = (16 * B) / (Real.pi * Real.arctan 2) := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using (mul_div_assoc B (16 : ℝ)
                      (Real.pi * Real.arctan 2)).symm
  simpa [B, mul_comm, mul_left_comm, mul_assoc] using hEq

lemma sixteen_Cpsi_mul_sqrt_le :
    (16 * C_psi_H1) * Real.sqrt (K0_paper + Kxi_paper)
      ≤ (42912 : ℝ) / 25000 := by
  have h_mul := mul_le_mul_of_nonneg_left four_Cpsi_mul_sqrt_le
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ))
  convert h_mul using 1
  · ring
  · norm_num

lemma sixteen_Cpsi_mul_sqrt_lt :
    (16 * C_psi_H1) * Real.sqrt (K0_paper + Kxi_paper)
      < (Real.pi * Real.arctan 2) / 2 := by
  have h_le := sixteen_Cpsi_mul_sqrt_le
  have h_bound : (42912 : ℝ) / 25000 < (Real.pi * Real.arctan 2) / 2 := by
    have h_step : (42912 : ℝ) / 25000 < (1727 : ℝ) / 1000 := by norm_num
    have h_pi_lower : (157 : ℝ) / 50 < Real.pi := by
      convert pi_gt_314 using 1 ; norm_num
    have h_arctan_lower : (11 : ℝ) / 10 < Real.arctan 2 := by
      simpa [show (1.1 : ℝ) = (11 : ℝ) / 10 by norm_num]
        using arctan_two_gt_one_point_one
    have h_prod : (1727 : ℝ) / 500 < Real.pi * Real.arctan 2 := by
      have h_prod1 : (157 : ℝ) / 50 * ((11 : ℝ) / 10)
          < Real.pi * ((11 : ℝ) / 10) :=
        mul_lt_mul_of_pos_right h_pi_lower (by norm_num : (0 : ℝ) < (11 : ℝ) / 10)
      have h_prod2 : Real.pi * ((11 : ℝ) / 10)
          < Real.pi * Real.arctan 2 :=
        mul_lt_mul_of_pos_left h_arctan_lower Real.pi_pos
      have h_eq : (157 : ℝ) / 50 * ((11 : ℝ) / 10) = (1727 : ℝ) / 500 := by norm_num
      exact lt_trans (by simpa [h_eq] using h_prod1)
        (by simpa [h_eq] using h_prod2)
    have h_div : (1727 : ℝ) / 1000 < (Real.pi * Real.arctan 2) / 2 := by
      have h_half_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      have := mul_lt_mul_of_pos_left h_prod h_half_pos
      have h_left : (1 / 2 : ℝ) * ((1727 : ℝ) / 500) = (1727 : ℝ) / 1000 := by
        norm_num
      rw [h_left] at this
      convert this using 1
      ring
    exact lt_trans h_step h_div
  have h_bound' : (16 * C_psi_H1) * Real.sqrt (K0_paper + Kxi_paper)
      < (1 / 2 : ℝ) * (Real.pi * Real.arctan 2) :=
    lt_of_le_of_lt h_le (by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h_bound)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using h_bound'

/-! ## Section 3: Υ Computation (YOUR RH-Specific Arithmetic)

This section computes Υ < 1/2, which is the key RH-specific arithmetic
showing your constants close the wedge.
-/

/-- M_ψ = (4/pi)·C_ψ^(H¹)·√(K₀+Kξ) -/
noncomputable def M_psi_paper : ℝ :=
  (4 / Real.pi) * C_psi_H1 * Real.sqrt C_box_paper

/-- Υ = (2/pi)·M_ψ/c₀ (wedge parameter from paper) -/
noncomputable def Upsilon_paper : ℝ :=
  (2 / Real.pi) * M_psi_paper / c0_paper

/-! ### Parameterized arithmetic in Kξ

We expose a parameterized Υ(Kξ) and a computable threshold `Kxi_max` so that
the closure condition is equivalent to `Kξ < Kxi_max`.
-/

/-- Parameterized wedge parameter Υ(Kξ) with paper constants and variable Kξ. -/
noncomputable def Upsilon_of (Kxi : ℝ) : ℝ :=
  (2 / Real.pi) * ((4 / Real.pi) * C_psi_H1 * Real.sqrt (K0_paper + Kxi)) / c0_paper

/-- Threshold for Kξ ensuring Υ(Kξ) < 1/2. -/
noncomputable def Kxi_max : ℝ :=
  ((Real.pi * Real.arctan 2) / (32 * C_psi_H1)) ^ 2 - K0_paper

/-- Standard numerical computation: Υ < 1/2.
Expands to: (2/pi) * ((4/pi) * 0.24 * √0.19486808) / ((arctan 2)/(2pi)) < 0.5
Simplifies to: (2/pi)² * 0.24 * √0.19486808 / arctan(2) < 0.5

This is pure numerical arithmetic. We admit it pending rigorous bounds on arctan(2) and sqrt.
BLOCKER-12: Needs lower bound on arctan(2) (we have arctan(2) > 1.1 pending) and
numeric sqrt evaluation.
-/
theorem upsilon_paper_lt_half : Upsilon_paper < 1 / 2 := by
  unfold Upsilon_paper M_psi_paper c0_paper C_box_paper K0_paper Kxi_paper C_psi_H1
  have h_den_pos : 0 < Real.pi * Real.arctan 2 :=
    mul_pos Real.pi_pos (by
      have : (0 : ℝ) < 2 := by norm_num
      have hmono : StrictMono Real.arctan := Real.arctan_strictMono
      have : Real.arctan 0 < Real.arctan 2 := hmono this
      simp)
  have h_bound := sixteen_Cpsi_mul_sqrt_lt
  have h_ratio := upsilon_ratio_eq
  have h_div :
      (16 * C_psi_H1 * Real.sqrt (K0_paper + Kxi_paper)) /
          (Real.pi * Real.arctan 2) < (1 / 2 : ℝ) :=
    (div_lt_iff₀ h_den_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_bound)
  -- The equality h_ratio shows the LHS expression equals the simplified form
  -- We've proven the simplified form < 1/2, so the original expression < 1/2
  calc 2 / Real.pi * (4 / Real.pi * 0.24 * √(3486808e-8 + 0.16)) / (Real.arctan 2 / (2 * Real.pi))
      = (16 * C_psi_H1 * Real.sqrt (K0_paper + Kxi_paper)) / (Real.pi * Real.arctan 2) := h_ratio
    _ < 1 / 2 := h_div

/-- Main computation: Υ < 1/2 (YOUR RH-specific result).

This is the key arithmetic showing your constants work:
- c₀ = (arctan 2)/(2pi) ≈ 0.176 (proven in ACTION 3)
- K₀ = 0.03486808 (from paper)
- Kξ = 0.16 (from unconditional VK bounds)
- C_ψ = 0.24 (from paper)
- C_box = K₀ + Kξ = 0.19486808

This is standard arithmetic but requires careful setup in Lean.
-/
theorem upsilon_less_than_half : Upsilon_paper < 1/2 :=
  upsilon_paper_lt_half

/-! Relate `Upsilon_of Kxi_paper` to `Upsilon_paper` and show the parameterized
ratio identity used in the closure test. -/

lemma upsilon_ratio_eq_param (Kxi : ℝ) :
  ((2 / Real.pi) * ((4 / Real.pi) * C_psi_H1 *
      Real.sqrt (K0_paper + Kxi))) /
      ((Real.arctan 2) / (2 * Real.pi))
    = (16 * C_psi_H1 * Real.sqrt (K0_paper + Kxi)) /
      (Real.pi * Real.arctan 2) := by
  -- identical algebra as `upsilon_ratio_eq`, parameterized by Kxi
  set B := C_psi_H1 * Real.sqrt (K0_paper + Kxi) with hB
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hatan_pos : 0 < Real.arctan (2 : ℝ) := by
    have hmono : StrictMono Real.arctan := Real.arctan_strictMono
    have : Real.arctan 0 < Real.arctan 2 := hmono (by norm_num)
    simp
  have hatan_ne : Real.arctan (2 : ℝ) ≠ 0 := ne_of_gt hatan_pos
  have hmain :
      ((2 / Real.pi) * (4 / Real.pi)) /
          ((Real.arctan 2) / (2 * Real.pi))
        = (16 : ℝ) / (Real.pi * Real.arctan 2) := by
    field_simp [hpi_ne, hatan_ne, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hEq :
      ((2 / Real.pi) * ((4 / Real.pi) * B)) /
          ((Real.arctan 2) / (2 * Real.pi))
        = (16 * B) / (Real.pi * Real.arctan 2) := by
    calc
      ((2 / Real.pi) * ((4 / Real.pi) * B)) /
            ((Real.arctan 2) / (2 * Real.pi))
          = (((2 / Real.pi) * (4 / Real.pi)) * B) /
              ((Real.arctan 2) / (2 * Real.pi)) := by
                simp [mul_comm, mul_assoc]
      _ = (B * ((2 / Real.pi) * (4 / Real.pi))) /
              ((Real.arctan 2) / (2 * Real.pi)) := by
                ring_nf
      _ = B * (((2 / Real.pi) * (4 / Real.pi)) /
              ((Real.arctan 2) / (2 * Real.pi))) := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using (mul_div_assoc B ((2 / Real.pi) * (4 / Real.pi))
                      ((Real.arctan 2) / (2 * Real.pi)))
      _ = B * ((16 : ℝ) / (Real.pi * Real.arctan 2)) := by
                simp [hmain]
      _ = (16 * B) / (Real.pi * Real.arctan 2) := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using (mul_div_assoc B (16 : ℝ)
                      (Real.pi * Real.arctan 2)).symm
  simpa [B, mul_comm, mul_left_comm, mul_assoc] using hEq

lemma Upsilon_of_eq_ratio (Kxi : ℝ) :
  Upsilon_of Kxi =
    ((16 * C_psi_H1 * Real.sqrt (K0_paper + Kxi)) / (Real.pi * Real.arctan 2)) := by
  unfold Upsilon_of c0_paper
  -- Rewrite via the parameterized ratio identity
  have := upsilon_ratio_eq_param Kxi
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using this

lemma Upsilon_of_at_paper : Upsilon_of Kxi_paper = Upsilon_paper := by
  unfold Upsilon_of Upsilon_paper M_psi_paper C_box_paper
  -- sqrt(C_box_paper) = sqrt(K0_paper + Kxi_paper)
  simp

/-- Closure test in terms of Kξ: if `Kξ < Kxi_max` then `Υ(Kξ) < 1/2`. -/
theorem upsilon_param_lt_half_of_Kxi_lt_max
  {Kxi : ℝ} (hKxi_nonneg : 0 ≤ Kxi) (hKxi_lt : Kxi < Kxi_max) :
  Upsilon_of Kxi < 1 / 2 := by
  -- Convert the threshold to a bound on 16·Cψ·√(K0+Kξ)
  have hK0_nonneg : 0 ≤ K0_paper := by norm_num [K0_paper]
  have hsum_nonneg : 0 ≤ K0_paper + Kxi := add_nonneg hK0_nonneg hKxi_nonneg
  have hRpos : 0 < (Real.pi * Real.arctan 2) / (32 * C_psi_H1) := by
    have hpos1 : 0 < Real.pi := Real.pi_pos
    have hpos2 : 0 < Real.arctan 2 := by
      have hmono : StrictMono Real.arctan := Real.arctan_strictMono
      have : Real.arctan 0 < Real.arctan 2 := hmono (by norm_num)
      simp
    have hpos3 : 0 < 32 * C_psi_H1 := by norm_num [C_psi_H1]
    have hnum_pos : 0 < Real.pi * Real.arctan 2 := mul_pos hpos1 hpos2
    exact div_pos hnum_pos hpos3
  -- From Kxi < Kxi_max, deduce √(K0+Kxi) < (pi·arctan 2)/(32·Cψ)
  have hsqrt_lt :
      Real.sqrt (K0_paper + Kxi)
        < (Real.pi * Real.arctan 2) / (32 * C_psi_H1) := by
    have hlt_sq : K0_paper + Kxi
        < ((Real.pi * Real.arctan 2) / (32 * C_psi_H1)) ^ 2 := by
      -- unpack Kxi_max definition
      have := hKxi_lt
      have hdef : Kxi_max = ((Real.pi * Real.arctan 2) / (32 * C_psi_H1)) ^ 2 - K0_paper := rfl
      -- Kxi < R^2 − K0 ⇒ K0 + Kxi < R^2
      rw [hdef] at this
      linarith
    -- Use sqrt monotonicity on nonnegatives
    have hsum_nonneg' : 0 ≤ K0_paper + Kxi := hsum_nonneg
    have _ : 0 ≤ ((Real.pi * Real.arctan 2) / (32 * C_psi_H1)) ^ 2 := by
      exact sq_nonneg _
    -- sqrt_lt_iff for nonnegatives
    have := (Real.sqrt_lt_sqrt_iff hsum_nonneg').mpr hlt_sq
    -- sqrt(R^2) = |R| = R since R>0
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hRpos]
      using this
  -- Scale by 16·Cψ (positive)
  have hscale_pos : 0 < 16 * C_psi_H1 := by norm_num [C_psi_H1]
  have hprod_lt :
      (16 * C_psi_H1) * Real.sqrt (K0_paper + Kxi)
        < (16 * C_psi_H1) * ((Real.pi * Real.arctan 2) / (32 * C_psi_H1)) :=
    mul_lt_mul_of_pos_left hsqrt_lt hscale_pos
  have htarget :
      (16 * C_psi_H1) * ((Real.pi * Real.arctan 2) / (32 * C_psi_H1))
        = (Real.pi * Real.arctan 2) / 2 := by
    field_simp [C_psi_H1]; grind
  have hmain_lt :
      (16 * C_psi_H1) * Real.sqrt (K0_paper + Kxi)
        < (Real.pi * Real.arctan 2) / 2 := by
    simpa [htarget] using hprod_lt
  -- Convert to Υ(Kξ) < 1/2 using the ratio identity
  have h_den_pos : 0 < Real.pi * Real.arctan 2 := by
    exact mul_pos Real.pi_pos (by
      have hmono : StrictMono Real.arctan := Real.arctan_strictMono
      have : Real.arctan 0 < Real.arctan 2 := hmono (by norm_num)
      simp)
  have _ :
      ((16 * C_psi_H1 * Real.sqrt (K0_paper + Kxi)) /
        (Real.pi * Real.arctan 2)) < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ h_den_pos]
    -- (16*Cψ*√) < (1/2) * (pi·atan2)
    rw [one_div]; rw [@inv_mul_eq_div]
    exact hmain_lt
  -- Finish by rewriting Υ(Kξ)
  have := Upsilon_of_eq_ratio Kxi
  have := Upsilon_of_eq_ratio Kxi
  simp [this]; exact (div_lt_iff₀' h_den_pos).mpr hmain_lt


/-- Υ is positive (proven from positive constants) -/
lemma upsilon_positive : 0 < Upsilon_paper := by
  simp only [Upsilon_paper, M_psi_paper, c0_paper, C_box_paper, K0_paper, Kxi_paper, C_psi_H1]
  -- All constants are positive
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_c0_pos : 0 < c0_paper := c0_positive
  have h_C_psi_pos : 0 < (0.24 : ℝ) := by norm_num
  have h_K0_pos : 0 < (0.03486808 : ℝ) := by norm_num
  have h_Kxi_pos : 0 < (0.16 : ℝ) := by norm_num
  have h_Cbox_pos : 0 < K0_paper + Kxi_paper := by
    simp only [K0_paper, Kxi_paper]
    linarith [h_K0_pos, h_Kxi_pos]
  have h_sqrt_pos : 0 < Real.sqrt (K0_paper + Kxi_paper) := Real.sqrt_pos.mpr h_Cbox_pos
  -- M_psi = (4/pi)·C_psi·√C_box > 0
  have h_M_pos : 0 < (4 / Real.pi) * C_psi_H1 * Real.sqrt (K0_paper + Kxi_paper) := by
    apply mul_pos
    · apply mul_pos
      · apply div_pos; linarith; exact h_pi_pos
      · simp only [C_psi_H1]; exact h_C_psi_pos
    · exact h_sqrt_pos
  -- Υ = (2/pi)·M_psi/c0 > 0
  apply div_pos
  apply mul_pos
  · apply div_pos; linarith; exact h_pi_pos
  · exact h_M_pos
  · exact h_c0_pos

end RH.RS.BoundaryWedgeProof
