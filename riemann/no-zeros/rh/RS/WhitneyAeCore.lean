import rh.RS.Det2Outer
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi

/-!
Core (P+) predicate and Whitney a.e. facade shared by Route B and Boundary proof.

This small module isolates the boundary `(P+)` predicate for the canonical field
`F(z) := (2 : ℂ) * J_pinch det2 O z` for a fixed outer `O` witnessing
`|O| = |det₂/ξ_ext|` on the boundary, and a facade lemma that exposes
the a.e. boundary inequality from a `(P+)` witness. Keeping this separate allows
Route B and the boundary wedge module to depend on the same definition without
import cycles.
-/

noncomputable section

namespace RH.RS.WhitneyAeCore

open Real Complex
open MeasureTheory
open RH.AcademicFramework.HalfPlaneOuterV2 (boundary)

/-- Canonical outer choice for Route B: choose any RS `OuterHalfPlane` witness. -/
private noncomputable def O : ℂ → ℂ :=
  RH.RS.OuterHalfPlane.choose_outer RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/-- (P+): nonnegativity of the boundary real part a.e. for
`F_pinch det2 O` along `boundary t`. -/
def PPlus_holds (O : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) (boundary t)).re

/-- Alias of `(P+)` using the canonical chosen outer `O`. -/
def PPlus_canonical : Prop := PPlus_holds O

/-- Facade: unwrap the `(P+)` proposition into the raw a.e. inequality. -/
@[simp] theorem PPlus_canonical_ae :
  PPlus_canonical → (∀ᵐ t : ℝ,
    0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) (boundary t)).re) :=
  id

/-! A basic positivity lemma for the canonical choice `O`.

On the boundary line, our fixed witness satisfies
`O (boundary t) = det2 (boundary t) / riemannXi_ext (boundary t)` by definition
of `O_witness`. Thus `J_pinch det2 O (boundary t)` simplifies to either `1`
when `riemannXi_ext (boundary t) ≠ 0`, or to `0` when `riemannXi_ext (boundary t) = 0`
since division-by-zero is `0` in `ℂ`. In both cases, the real part of
`F := 2 · J_pinch` is nonnegative. This yields `(P+)` for the canonical boundary
field without importing any heavy wedge modules.
-/

theorem PPlus_canonical_proved_basic : PPlus_canonical := by
  classical
  -- Unfold the target `(P+)` predicate for the canonical `O`.
  dsimp [PPlus_canonical, PPlus_holds]
  -- Prove pointwise nonnegativity on the boundary; strengthen from a.e. to ∀.
  refine Filter.Eventually.of_forall (fun t => ?_)
  -- Set the boundary point and compute `F` there.
  set z : ℂ := boundary t
  have hz_re : z.re = (1/2 : ℝ) := by
    -- boundary t = 1/2 + i t
    have : z = (1/2 : ℂ) + Complex.I * (t : ℂ) := rfl
    simpa [this, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re]
  -- On the boundary, our chosen witness `O` coincides with `det2/ξ_ext` by construction.
  have hO_boundary : O z = RH.RS.det2 z / RH.AcademicFramework.CompletedXi.riemannXi_ext z := by
    -- boundary condition: (1/2 : ℝ) < z.re is false, so we take the ratio branch
    have hcond : ¬ ((1/2 : ℝ) < z.re) := by simpa [hz_re]
    -- Use definitional equality: the chosen outer comes from the witness `O_witness`
    -- so reducing at boundary yields the ratio form
    simpa [O,
           RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved,
           RH.RS.OuterHalfPlane.choose_outer,
           RH.RS.O_witness,
           hcond]
  -- Compute `F := 2 · J_pinch` on the boundary using `hO_boundary` and split on `ξ_ext z`.
  have hF_nonneg : 0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z).re := by
    -- Expand `F_pinch` and `J_pinch` at `z`.
    dsimp [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch,
           RH.AcademicFramework.HalfPlaneOuterV2.J_pinch]
    -- Case split on whether `ξ_ext z = 0`.
    by_cases hXi0 : RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0
    · -- Denominator zero ⇒ inverse is 0, so `J_pinch z = 0` and `F z = 0`.
      -- Therefore the real part is 0.
      simp [hO_boundary, hXi0]
    · -- Nonzero denominator: simplify using `hO_boundary` to get `J_pinch z = 1`.
      -- Then `F z = 2`, whose real part is nonnegative.
      have hden : O z * RH.AcademicFramework.CompletedXi.riemannXi_ext z ≠ 0 := by
        -- From `hO_boundary` and `hXi0 ≠ 0`, we have `O z = det2 z / ξ_ext z`, hence
        -- `O z * ξ_ext z = det2 z`, and `det2` is nonzero on the boundary line.
        -- Use the RS-side nonvanishing along Re = 1/2.
        have hdet_ne : RH.RS.det2 z ≠ 0 := by
          -- `z = 1/2 + i t` by construction; apply the RS lemma on the critical line.
          have hb : z = RH.RS.boundary t := rfl
          simpa [hb] using RH.RS.det2_nonzero_on_critical_line t
        -- Show the product is `det2 z` and use its nonvanishing.
        have : O z * RH.AcademicFramework.CompletedXi.riemannXi_ext z = RH.RS.det2 z := by
          -- Multiply both sides of `hO_boundary` by `riemannXi_ext z`.
          have hXi_ne : RH.AcademicFramework.CompletedXi.riemannXi_ext z ≠ 0 := hXi0
          have : O z * RH.AcademicFramework.CompletedXi.riemannXi_ext z
              = (RH.RS.det2 z / RH.AcademicFramework.CompletedXi.riemannXi_ext z)
                * RH.AcademicFramework.CompletedXi.riemannXi_ext z := by simpa [hO_boundary]
          -- Simplify `a / b * b = a` when `b ≠ 0`.
          simpa [div_eq_mul_inv, inv_mul_cancel hXi_ne] using this
        simpa [this]
      -- With a nonzero denominator and `hO_boundary`, `J_pinch z = 1`.
      have hJ : RH.RS.det2 z / (O z * RH.AcademicFramework.CompletedXi.riemannXi_ext z) = 1 := by
        -- Rewrite denominator as `det2 z` using the computation above.
        have : O z * RH.AcademicFramework.CompletedXi.riemannXi_ext z = RH.RS.det2 z := by
          -- Same computation as above; re-prove locally.
          have hXi_ne : RH.AcademicFramework.CompletedXi.riemannXi_ext z ≠ 0 := hXi0
          have : O z * RH.AcademicFramework.CompletedXi.riemannXi_ext z
              = (RH.RS.det2 z / RH.AcademicFramework.CompletedXi.riemannXi_ext z)
                * RH.AcademicFramework.CompletedXi.riemannXi_ext z := by simpa [hO_boundary]
          simpa [div_eq_mul_inv, inv_mul_cancel hXi_ne]
        -- Now `det2 z / det2 z = 1`.
        simpa [this]
      -- Finish: real part of `(2 : ℂ) * 1` is `2`.
      simpa [hJ]
  -- Rewrite back to the target point `boundary t`.
  simpa [z] using hF_nonneg

end RH.RS.WhitneyAeCore
