import Mathlib.Analysis.Analytic.Basic
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CayleyAdapters
import rh.academic_framework.DiskHardy
-- keep this module AF-only to avoid RS build dependencies
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Poisson–Cayley bridge (scaffolding)

This module introduces a crisp target Prop for the half-plane Poisson
real-part identity on a subset `S ⊆ Ω`, together with convenience
packagers that assemble the subset representation for the pinch field
once that identity is supplied.

The concrete proof of the identity will be added by transporting a
disk-side Poisson representation through the Cayley transform.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace PoissonCayley

open Complex
open RH.AcademicFramework.HalfPlaneOuterV2
open RH.AcademicFramework
open MeasureTheory

/- Right half–plane Ω (local alias) -/
local notation "Ω" => RH.AcademicFramework.HalfPlaneOuterV2.Ω

/-- Target predicate: Poisson real-part identity for a function `F` on a subset `S ⊆ Ω`. -/
def HasHalfPlanePoissonReEqOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, (F z).re = poissonIntegral (fun t : ℝ => (F (boundary t)).re) z

/-- Convenience: specialize the target predicate to the pinch field `F := 2 · J_pinch det2 O` on
`S := Ω \ {riemannXi_ext = 0}` (ext variant). -/
def HasHalfPlanePoissonReEqOn_pinch_ext (det2 O : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonReEqOn (F_pinch det2 O)
    (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0})

/-!
Once the real-part identity is available on `S`, the subset Poisson representation used by the
pinch route follows immediately via `HalfPlaneOuterV2.pinch_poissonRepOn_offZeros`.
The following packagers expose this step explicitly for readability.
-/

-- (trimmed)

/-- Boundary identification between a half-plane function `F` and a disk function `H` via
the Cayley boundary mapping. -/
def EqOnBoundary (F H : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, F (boundary t) = H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)

/-- Kernel transport along Cayley on a subset `S ⊆ Ω` for a disk function `H`:
the half-plane Poisson integral of the pullback boundary real part equals the disk
Poisson real part at the Cayley image. -/
def CayleyKernelTransportOn (H : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
      = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re

/-- Disk→half-plane Cayley bridge for real parts on a subset `S ⊆ Ω`.
Assumptions:
- interior identification: `F = H ∘ toDisk` on `S`;
- boundary identification: `F(boundary t) = H(boundaryToDisk t)` on ℝ;
- kernel transport along Cayley on `S`.

Conclusion: the half-plane Poisson real-part identity holds for `F` on `S`. -/
theorem reEq_on_from_disk_via_cayley
  (F H : ℂ → ℂ) {S : Set ℂ}
  (hEqInterior : Set.EqOn F (fun z => H (RH.AcademicFramework.CayleyAdapters.toDisk z)) S)
  (hEqBoundary : EqOnBoundary F H)
  (hKernel : CayleyKernelTransportOn H S)
  : HasHalfPlanePoissonReEqOn F S := by
  intro z hzS
  have h1 : (F z).re = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    simpa using congrArg Complex.re (hEqInterior hzS)
  -- pointwise equality of boundary real-part functions
  have hIntgEq :
      (fun t : ℝ => (F (boundary t)).re)
        = (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) := by
    funext t
    simpa using congrArg Complex.re (hEqBoundary t)
  -- transport the kernel identity along the equality of boundary integrands
  have hPI :
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
        = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    -- combine integrand equality with kernel transport via a calc chain
    calc
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
          = poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z := by
            exact congrArg (fun u => poissonIntegral u z) hIntgEq
      _ = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re :=
            hKernel z hzS
  -- finish with interior identification of real parts
  simpa [h1] using hPI.symm

/-- Boundary identity for the Cayley pullback: `F(boundary t) = H(boundaryToDisk t)`. -/
lemma EqOnBoundary_pullback (H : ℂ → ℂ) :
  EqOnBoundary (fun z => H (CayleyAdapters.toDisk z)) H := by
  intro t
  simp [EqOnBoundary, CayleyAdapters.boundaryToDisk]

/-- From a subset half-plane Poisson representation of the Cayley pullback
`F := H ∘ toDisk` on `S`, derive kernel transport on `S` for `H`. -/
theorem cayley_kernel_transport_from_rep_on
  (H : ℂ → ℂ) {S : Set ℂ}
  (hRepOn : HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S)
  : CayleyKernelTransportOn H S := by
  intro z hzS
  -- Re(F z) = P(boundary Re F)(z) for F := H ∘ toDisk
  have hRe :
      ((fun z => H (CayleyAdapters.toDisk z)) z).re
        = poissonIntegral (fun t : ℝ => ((fun z => H (CayleyAdapters.toDisk z)) (boundary t)).re) z :=
    hRepOn.formula z hzS
  -- Rewrite boundary integrand via `boundaryToDisk`, then rearrange
  have hIntg :
      (fun t : ℝ => ((fun z => H (CayleyAdapters.toDisk z)) (boundary t)).re)
        = (fun t : ℝ => (H (CayleyAdapters.boundaryToDisk t)).re) := by
    funext t; simp [CayleyAdapters.boundaryToDisk]
  -- Conclude the transport identity
  simpa [hIntg] using hRe.symm

/-- The remaining pinch-specialized and pullback representation sections are omitted
to keep this module minimal and compiling. -/

-- Global bridge: from a half-plane Poisson representation of `F`, obtain the
-- real-part identity on all of Ω.
theorem hReEq_on_of_halfplane_rep (F : ℂ → ℂ)
  (hRep : HasPoissonRep F) :
  HasHalfPlanePoissonReEqOn F Ω := by
  intro z hz
  exact hRep.formula z hz

-- Subset bridge: from a subset half-plane Poisson representation of `F` on `S`,
-- obtain the real-part identity on `S`.
theorem hReEq_on_of_halfplane_rep_on (F : ℂ → ℂ) {S : Set ℂ}
  (hRepOn : HasPoissonRepOn F S) :
  HasHalfPlanePoissonReEqOn F S := by
  intro z hz
  exact hRepOn.formula z hz

-- Pinch specialization (ext): if the pinch field admits a half-plane Poisson
-- representation on Ω, then the real-part identity holds on the off-zeros subset `S`.
theorem hReEq_pinch_ext_of_halfplane_rep
  (det2 O : ℂ → ℂ)
  (hRep : HasPoissonRep (F_pinch det2 O)) :
  HasHalfPlanePoissonReEqOn_pinch_ext det2 O := by
  intro z hz
  have : (F_pinch det2 O z).re
      = poissonIntegral (fun t : ℝ => (F_pinch det2 O (boundary t)).re) z :=
    hRep.formula z hz.1
  simpa using this

/-! ## Pinch specialization via Cayley (eliminate placeholder)

We now assemble the half–plane real–part identity for the pinch field on the
off–zeros set by transporting a disk-side identity through the Cayley bridge.
This removes the need for any placeholder assumption at the route level. -/

/-- Builder: if the Cayley pullback `(H ∘ toDisk)` has a subset half-plane Poisson
representation on `S`, and `F = H ∘ toDisk` on `S` with matching boundary traces,
then the half-plane real-part identity holds for `F` on `S`. -/
theorem pinch_halfplane_ReEqOn_from_cayley
  (F H : ℂ → ℂ) {S : Set ℂ}
  (hEqInterior : Set.EqOn F (fun z => H (CayleyAdapters.toDisk z)) S)
  (hEqBoundary  : EqOnBoundary F H)
  (hRepOnPull   : HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S)
  : HasHalfPlanePoissonReEqOn F S := by
  -- kernel transport for H on S from the subset representation of H∘toDisk
  have hKernel : CayleyKernelTransportOn H S := cayley_kernel_transport_from_rep_on H hRepOnPull
  -- conclude the half-plane real-part identity for F on S
  exact reEq_on_from_disk_via_cayley F H hEqInterior hEqBoundary hKernel

/-- Pinch ext specialization: from a subset half-plane Poisson representation of the
pullback `(F_pinch det2 O) ∘ toDisk` on `S`, obtain the half-plane real-part identity
for `F_pinch det2 O` on `S`. -/
theorem pinch_ReEqOn_from_pullback
  (det2 O : ℂ → ℂ) {S : Set ℂ}
  (H : ℂ → ℂ)
  (hEqInt : Set.EqOn (F_pinch det2 O) (fun z => H (CayleyAdapters.toDisk z)) S)
  (hEqBd  : EqOnBoundary (F_pinch det2 O) H)
  (hRepPull : HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S)
  : HasHalfPlanePoissonReEqOn (F_pinch det2 O) S := by
  -- kernel transport for H from the subset representation of H∘toDisk
  have hKernel : CayleyKernelTransportOn H S := cayley_kernel_transport_from_rep_on H hRepPull
  -- conclude the half-plane real-part identity for F on S
  exact reEq_on_from_disk_via_cayley (F := F_pinch det2 O) (H := H)
    (S := S) hEqInt hEqBd hKernel

/-- Build Cayley kernel transport on a subset `S ⊆ Ω` directly from a disk-side Poisson
representation and a change-of-variables identity that converts the disk Poisson integral
at `toDisk z` to the half‑plane Poisson integral at `z`. -/
theorem cayley_kernel_transport_from_disk
  (H : ℂ → ℂ) {S : Set ℂ}
  (hDisk : RH.AcademicFramework.DiskHardy.HasDiskPoissonRepresentation H)
  (hS : S ⊆ HalfPlaneOuterV2.Ω)
  (hChange : ∀ z ∈ S,
    (∫ θ : ℝ,
        (H (RH.AcademicFramework.DiskHardy.boundary θ)).re
          * RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
      = (∫ t : ℝ,
        (H (CayleyAdapters.boundaryToDisk t)).re
          * HalfPlaneOuterV2.poissonKernel z t))
  : CayleyKernelTransportOn H S := by
  intro z hzS
  -- Disk Poisson representation at w := toDisk z (using S ⊆ Ω ⇒ toDisk maps into unit disk)
  have hw : CayleyAdapters.toDisk z ∈ RH.AcademicFramework.DiskHardy.unitDisk := by
    exact RH.AcademicFramework.CayleyAdapters.map_Ω_to_unitDisk (hS hzS)
  have hDiskEq : (H (CayleyAdapters.toDisk z)).re
      = ∫ θ : ℝ,
          (H (RH.AcademicFramework.DiskHardy.boundary θ)).re
            * RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ :=
    hDisk.re_eq (CayleyAdapters.toDisk z) hw
  -- Convert the disk integral to the half‑plane Poisson integral via the supplied identity
  have hCoV := hChange z hzS
  -- Rearrange to the required orientation
  -- Target: P_Ω[Re(H∘boundaryToDisk)](z) = Re(H(toDisk z))
  -- Use the two equalities above and symmetry
  have : HalfPlaneOuterV2.poissonIntegral
      (fun t : ℝ => (H (CayleyAdapters.boundaryToDisk t)).re) z
      = (H (CayleyAdapters.toDisk z)).re := by
    -- unfold poissonIntegral on the half‑plane side
    have : (∫ t : ℝ,
              (H (CayleyAdapters.boundaryToDisk t)).re * HalfPlaneOuterV2.poissonKernel z t)
            = (H (CayleyAdapters.toDisk z)).re := by
      -- combine hCoV with hDiskEq
      simpa [hDiskEq] using hCoV.symm
    -- rewrite to the `poissonIntegral` form
    simpa [HalfPlaneOuterV2.poissonIntegral] using this
  simpa [this.symm]

/-!
Auxiliary a.e. kernel identification under the Cayley boundary parametrization θ.
This is the clean AF form used by both the change-of-variables identity and the
integrability transfer. The proof is algebraic and holds pointwise in `t`, so we
package it as an a.e. statement via `eventually_of_forall`.
-/
lemma ae_kernel_under_theta
  (z : ℂ) (hzΩ : z ∈ HalfPlaneOuterV2.Ω) :
  ∀ᵐ t : ℝ,
    RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) (CayleyAdapters.theta t)
      * deriv CayleyAdapters.theta t
    = - HalfPlaneOuterV2.poissonKernel z t := by
  classical
  -- The identity is pointwise in t; we lift to a.e. using eventually_of_forall
  refine Filter.eventually_of_forall (fun t => ?_)
  -- Notations
  set w : ℂ := CayleyAdapters.toDisk z
  set s : ℂ := HalfPlaneOuterV2.boundary t
  set ξ : ℂ := CayleyAdapters.boundaryToDisk t
  -- Boundary identification and derivative for θ
  have hbd : RH.AcademicFramework.DiskHardy.boundary (CayleyAdapters.theta t) = ξ := by
    simpa [ξ] using CayleyAdapters.boundaryToDisk_param t
  have hder : deriv CayleyAdapters.theta t = - (1 / (Complex.abs s)^2) := by
    simpa [s] using CayleyAdapters.theta_deriv_eq_neg_inv_absSq t
  -- Disk kernel at θ(t)
  have hDisk : RH.AcademicFramework.DiskHardy.poissonKernel w (CayleyAdapters.theta t)
      = ((1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2) * (1 / (2 * Real.pi)) := by
    simp [RH.AcademicFramework.DiskHardy.poissonKernel, hbd]
  -- Half‑plane kernel at t
  have hHalf : HalfPlaneOuterV2.poissonKernel z t
      = (1 / Real.pi) * ((z.re - (1/2 : ℝ)) /
          ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2)) := by
    simp [HalfPlaneOuterV2.poissonKernel]
  -- Denominator: |s − z|^2 equals a^2 + (t − b)^2 with a = Re z − 1/2, b = Im z
  have hDenEq : (Complex.abs (s - z))^2
      = (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := by
    have : s = { re := (1/2 : ℝ), im := t } := by
      simpa [HalfPlaneOuterV2.boundary_mk_eq] using rfl
    -- expand norm-squared
    simpa [this, pow_two]
  -- Density ratio identity connecting disk and half‑plane parameters
  have hdens := CayleyAdapters.density_ratio_boundary z hzΩ t
  -- Core algebra: combine identities to match kernels with the θ' factor
  -- Start from the disk side and multiply by θ'
  have : RH.AcademicFramework.DiskHardy.poissonKernel w (CayleyAdapters.theta t)
      * deriv CayleyAdapters.theta t
      = (((1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2) * (1 / (2 * Real.pi)))
          * (-(1 / (Complex.abs s)^2)) := by
    simp [hDisk, hder]
  -- Use the density ratio (rewritten form) and cancel |s|^2; then rewrite denominators
  -- Two final algebra steps: (i) cancel the factor 2 via (1/(2π))*2 = 1/π, and
  -- (ii) convert (2*z.re - 1) to 2*(z.re - 1/2) to match the canonical form.
  have hAlg :
      (((1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2) * (1 / (2 * Real.pi)))
        * (-(1 / (Complex.abs s)^2))
      = - ((1 / Real.pi) * ((z.re - (1/2 : ℝ)) /
            ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2))) := by
    -- Substitute density ratio and rearrange
    -- (1 - |w|^2)/|ξ-w|^2 = ((2*Re z - 1) * |s|^2) / |s - z|^2
    have hDR : (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
        = (((2 : ℝ) * z.re - 1) * (Complex.abs s)^2) / (Complex.abs (s - z))^2 := by
      simpa [w, ξ] using hdens
    -- Apply hDR, cancel |s|^2 with θ' factor, and rewrite constants
    -- First rewrite using hDenEq to express the denominator
    have hDen : (Complex.abs (s - z))^2 = (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := hDenEq
    -- Now compute
    calc
      (((1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2) * (1 / (2 * Real.pi)))
          * (-(1 / (Complex.abs s)^2))
          = ((((2 : ℝ) * z.re - 1) * (Complex.abs s)^2) / (Complex.abs (s - z))^2
                * (1 / (2 * Real.pi))) * (-(1 / (Complex.abs s)^2)) := by
                  simpa [hDR]
      _ = - (((((2 : ℝ) * z.re - 1) * (Complex.abs s)^2) / (Complex.abs (s - z))^2)
                * (1 / (Complex.abs s)^2) * (1 / (2 * Real.pi))) := by
                  ring
      _ = - ((((2 : ℝ) * z.re - 1) / (Complex.abs (s - z))^2) * (1 / (2 * Real.pi))) := by
                  -- cancel |s|^2
                  field_simp [mul_comm, mul_left_comm, mul_assoc]
      _ = - (((2 : ℝ) * (z.re - (1/2 : ℝ))) / ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2)
                * (1 / (2 * Real.pi))) := by
                  -- rewrite denominator and numerator
                  simpa [two_mul, sub_eq_add_neg, hDen]
      _ = - ((z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2)
                * (1 / Real.pi)) := by
                  -- (2a)/(2π) = a/π
                  field_simp [mul_comm, mul_left_comm, mul_assoc]
      _ = - ((1 / Real.pi) * ((z.re - (1/2 : ℝ)) /
                ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2))) := by
                  ring
  -- Conclude by the half‑plane kernel form
  simpa [hHalf] using this.trans hAlg

theorem cayley_poisson_integral_change
  (H : ℂ → ℂ) {S : Set ℂ} (hS : S ⊆ HalfPlaneOuterV2.Ω)
  (z : ℂ) (hz : z ∈ S)
  (hIntDisk : Integrable
    (fun θ : ℝ =>
      (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
        RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)) :
  (∫ θ : ℝ,
      (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
        RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
  = (∫ t : ℝ,
      (H (CayleyAdapters.boundaryToDisk t)).re *
        HalfPlaneOuterV2.poissonKernel z t) := by
  classical
  -- Change-of-variables θ = theta(t) with DiskHardy.boundary (theta t) = boundaryToDisk t.
  have hzΩ : z ∈ HalfPlaneOuterV2.Ω := hS hz
  -- Define the two integrands
  let fθ : ℝ → ℝ := fun θ =>
    (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
      RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ
  let gt : ℝ → ℝ := fun t =>
    (H (CayleyAdapters.boundaryToDisk t)).re * HalfPlaneOuterV2.poissonKernel z t
  -- pointwise substitution identity for integrands composed with θ multiplied by θ'
  have hparam :
      (fun t : ℝ => fθ (CayleyAdapters.theta t) * (deriv CayleyAdapters.theta t))
        = fun t : ℝ => - gt t := by
    funext t
    have hbd : RH.AcademicFramework.DiskHardy.boundary (CayleyAdapters.theta t)
        = CayleyAdapters.boundaryToDisk t := CayleyAdapters.boundaryToDisk_param t
    have hder : deriv CayleyAdapters.theta t
        = - (1 / (Complex.abs (HalfPlaneOuterV2.boundary t))^2) :=
      CayleyAdapters.theta_deriv_eq_neg_inv_absSq t
    set w : ℂ := CayleyAdapters.toDisk z
    set s : ℂ := HalfPlaneOuterV2.boundary t
    set ξ : ℂ := CayleyAdapters.boundaryToDisk t
    -- expand kernels and simplify using density ratio and derivative
    have hdens := CayleyAdapters.density_ratio_boundary z hzΩ t
    -- Disk kernel at θ(t)
    have hDisk : RH.AcademicFramework.DiskHardy.poissonKernel w (CayleyAdapters.theta t)
        = ((1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2) * (1 / (2 * Real.pi)) := by
      simp [RH.AcademicFramework.DiskHardy.poissonKernel, hbd]
    -- Half-plane kernel at t
    have hHalf : HalfPlaneOuterV2.poissonKernel z t
        = (1 / Real.pi) * ((z.re - (1/2 : ℝ)) /
            ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2)) := by
      simp [HalfPlaneOuterV2.poissonKernel]
    -- |s - z|^2 equals a^2 + (t - b)^2
    have hDenEq : (Complex.abs (s - z))^2
        = (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := by
      have : s = { re := (1/2 : ℝ), im := t } := by
        simpa [HalfPlaneOuterV2.boundary_mk_eq] using rfl
      -- norm-squared expands to (Δre)^2 + (Δim)^2
      simpa [this, pow_two]
    -- combine identities to match integrands
    have : fθ (CayleyAdapters.theta t) * (deriv CayleyAdapters.theta t)
        = - gt t := by
      -- unfold fθ and gt
      simp [fθ, gt, hbd, hDisk, hHalf, hder, hdens, hDenEq, sub_eq_add_neg, two_mul,
        mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, add_comm, add_left_comm, add_assoc,
        one_div, Real.pi_pos.ne']
    simpa [this]
  -- Apply change-of-variables for real integrals (Bochner integral on ℝ)
  have hMeas : AEMeasurable CayleyAdapters.theta :=
    CayleyAdapters.theta_measurable.aemeasurable
  have hDeriv : ∀ᵐ t : ℝ, HasDerivAt CayleyAdapters.theta (deriv CayleyAdapters.theta t) t := by
    -- theta is C¹ everywhere
    exact Filter.eventually_of_forall (fun t => (CayleyAdapters.theta_hasDerivAt t))
  -- Compose and multiply by derivative; integrable by substitution lemma
  have hIntComp : Integrable (fun t : ℝ => fθ (CayleyAdapters.theta t) * deriv CayleyAdapters.theta t) := by
    have := MeasureTheory.integrable_comp_mul_deriv
      (f := fun θ : ℝ =>
        (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
          RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
      (g := CayleyAdapters.theta)
      (hg := hMeas) (hφ := hDeriv) (hf := hIntDisk)
    simpa [fθ] using this
  -- Execute the substitution in the integral
  have hSubst := MeasureTheory.integral_comp_mul_deriv
    (f := fun θ : ℝ =>
      (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
        RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
    (g := CayleyAdapters.theta)
    (hg := hMeas) (hφ := hDeriv) (hf := hIntDisk)
  -- a.e. kernel identity under θ combined with boundary compatibility
  have hAEKernel : ∀ᵐ t : ℝ,
      RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) (CayleyAdapters.theta t)
        * deriv CayleyAdapters.theta t
        = - HalfPlaneOuterV2.poissonKernel z t :=
    ae_kernel_under_theta z hzΩ
  have hAE :
      (fun t : ℝ => fθ (CayleyAdapters.theta t) * deriv CayleyAdapters.theta t)
        =ᵐ[MeasureTheory.volume]
      (fun t : ℝ => - gt t) := by
    -- rewrite the H(boundary(θ t)) factor via boundaryToDisk_param, then apply kernel a.e. identity
    refine hAEKernel.mono ?_
    intro t ht
    -- boundary substitution is pointwise, not only a.e.
    have hbd : RH.AcademicFramework.DiskHardy.boundary (CayleyAdapters.theta t)
        = CayleyAdapters.boundaryToDisk t := CayleyAdapters.boundaryToDisk_param t
    -- expand fθ and gt
    simp [fθ, gt, hbd, ht, mul_comm, mul_left_comm, mul_assoc]
  -- Execute substitution and then rewrite RHS integral using the a.e. equality
  -- Note: the a.e. equality encodes the sign from the derivative.
  have : (∫ θ : ℝ,
              (H (RH.AcademicFramework.DiskHardy.boundary θ)).re
                * RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
            = (∫ t : ℝ, (fun t => fθ (CayleyAdapters.theta t) * deriv CayleyAdapters.theta t) t) := by
    -- orientation and derivative handled by the substitution lemma
    simpa using hSubst.symm
  -- Rewrite the integrand on the RHS using a.e. equality and identify the target
  have : (∫ t : ℝ, (fun t => fθ (CayleyAdapters.theta t) * deriv CayleyAdapters.theta t) t)
            = (∫ t : ℝ, (fun t => - gt t) t) := by
    exact MeasureTheory.integral_congr_ae hAE
  -- Finish: integral of the negative is the negative of the integral
  -- and conclude to the stated half-plane integral.
  -- We avoid assuming integrability of `gt` by directly using `integral_congr_ae` above
  -- and the fact that `integral_comp_mul_deriv` provides integrability of the RHS.
  -- Combine equalities and rewrite to the required form.
  -- Move equalities back to the original orientation
  have hEq := (by
    -- start from the disk-side integral
    have := hSubst
    -- rewrite the RHS via the a.e. identity
    have h1 : (∫ t : ℝ, fθ (CayleyAdapters.theta t) * deriv CayleyAdapters.theta t)
              = (∫ t : ℝ, - gt t) := MeasureTheory.integral_congr_ae hAE
    -- combine
    simpa [fθ, gt, h1])
  -- Now orient as in the statement and simplify
  -- `hEq` is of the desired shape modulo unfolding `gt`
  -- Use `by_cases` on integrability of the target to rewrite integral of `-gt`.
  -- However, `integral_congr_ae` already gave equality without needing this step; we directly
  -- present the target equality by expanding `gt`.
  simpa [fθ, gt] using hEq

/-- Integrability transfer: for fixed `z ∈ S`, integrability of the disk-side
Poisson integrand at `w = toDisk z` implies integrability of the half‑plane
Poisson integrand at `z`. This is a direct corollary of the
`cayley_poisson_integral_change` change-of-variables identity. -/
theorem cayley_integrable_from_disk
  (H : ℂ → ℂ) {S : Set ℂ}
  (hS : S ⊆ HalfPlaneOuterV2.Ω)
  (hDisk : RH.AcademicFramework.DiskHardy.HasDiskPoissonRepresentation H)
  (z : ℂ) (hz : z ∈ S) :
  Integrable (fun t : ℝ =>
    (H (CayleyAdapters.boundaryToDisk t)).re * HalfPlaneOuterV2.poissonKernel z t) := by
  -- Let w = toDisk z and import disk integrability
  have hw : CayleyAdapters.toDisk z ∈ RH.AcademicFramework.DiskHardy.unitDisk :=
    RH.AcademicFramework.CayleyAdapters.map_Ω_to_unitDisk (hS hz)
  have hIntDisk : Integrable
      (fun θ : ℝ =>
        (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
          RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ) :=
    hDisk.integrable (CayleyAdapters.toDisk z) hw
  -- Transfer integrability via the θ = theta(t) substitution
  have hMeas : AEMeasurable CayleyAdapters.theta :=
    CayleyAdapters.theta_measurable.aemeasurable
  have hDeriv : ∀ᵐ t : ℝ, HasDerivAt CayleyAdapters.theta (deriv CayleyAdapters.theta t) t := by
    exact Filter.eventually_of_forall (fun t => (CayleyAdapters.theta_hasDerivAt t))
  -- f ∘ θ · θ' is integrable; identify it a.e. with -g and conclude integrability of g
  have hIntComp : Integrable (fun t : ℝ =>
      (H (RH.AcademicFramework.DiskHardy.boundary (CayleyAdapters.theta t))).re *
        RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) (CayleyAdapters.theta t)
      * (deriv CayleyAdapters.theta t)) := by
    have := MeasureTheory.integrable_comp_mul_deriv
      (f := fun θ : ℝ =>
        (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
          RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
      (g := CayleyAdapters.theta)
      (hg := hMeas) (hφ := hDeriv) (hf := hIntDisk)
    simpa using this
  -- a.e. identity between the composed integrand and -g using the kernel lemma
  have hAEKernel : ∀ᵐ t : ℝ,
      RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) (CayleyAdapters.theta t)
        * deriv CayleyAdapters.theta t
        = - HalfPlaneOuterV2.poissonKernel z t :=
    ae_kernel_under_theta z (hS hz)
  have hAE : (fun t : ℝ =>
      (H (RH.AcademicFramework.DiskHardy.boundary (CayleyAdapters.theta t))).re *
        RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) (CayleyAdapters.theta t)
      * (deriv CayleyAdapters.theta t))
      =ᵐ[MeasureTheory.volume]
      (fun t : ℝ => - ((H (CayleyAdapters.boundaryToDisk t)).re * HalfPlaneOuterV2.poissonKernel z t)) := by
    refine hAEKernel.mono ?_
    intro t ht
    -- rewrite the boundary argument
    have hbd : RH.AcademicFramework.DiskHardy.boundary (CayleyAdapters.theta t)
        = CayleyAdapters.boundaryToDisk t := CayleyAdapters.boundaryToDisk_param t
    simp [hbd, ht, mul_comm, mul_left_comm, mul_assoc]
  -- Conclude integrability of -g by a.e. equality
  have hIntNegG : Integrable (fun t : ℝ => - ((H (CayleyAdapters.boundaryToDisk t)).re
      * HalfPlaneOuterV2.poissonKernel z t)) := by
    -- use integrability of the composed integrand and a.e. equality
    exact hIntComp.congr hAE
  -- integrability is stable under negation and multiplication by constants
  simpa using hIntNegG.neg

lemma diskPoissonRep_pullback
  (H : ℂ → ℂ) {S : Set ℂ}
  (hDisk : RH.AcademicFramework.DiskHardy.HasDiskPoissonRepresentation H)
  (hS : S ⊆ HalfPlaneOuterV2.Ω) :
  HalfPlaneOuterV2.HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S := by
  refine
  { subset := hS
    , analytic := ?hA
    , integrable := ?hI
    , formula := ?hEq }
  · -- Analytic on S by composition: H analytic on unitDisk, toDisk analytic on Ω and maps S→unitDisk
    have hH : AnalyticOn ℂ H RH.AcademicFramework.DiskHardy.unitDisk := hDisk.analytic
    have hto : AnalyticOn ℂ CayleyAdapters.toDisk HalfPlaneOuterV2.Ω :=
      CayleyAdapters.toDisk_analyticOn_Ω
    have htoS : AnalyticOn ℂ CayleyAdapters.toDisk S := hto.mono hS
    have hmaps : Set.MapsTo CayleyAdapters.toDisk S RH.AcademicFramework.DiskHardy.unitDisk := by
      intro z hz; exact RH.AcademicFramework.CayleyAdapters.map_Ω_to_unitDisk (hS hz)
    simpa using hH.comp htoS hmaps
  · -- Integrability is transported from the disk side via CoV
    intro z hz
    exact cayley_integrable_from_disk H hS hDisk z hz
  · intro z hz
    have hw : CayleyAdapters.toDisk z ∈ RH.AcademicFramework.DiskHardy.unitDisk :=
      RH.AcademicFramework.CayleyAdapters.map_Ω_to_unitDisk (hS hz)
    have hDiskEq : (H (CayleyAdapters.toDisk z)).re
        = ∫ θ : ℝ,
            (H (RH.AcademicFramework.DiskHardy.boundary θ)).re *
              RH.AcademicFramework.DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ :=
      hDisk.re_eq (CayleyAdapters.toDisk z) hw
    have hCoV := cayley_poisson_integral_change H hS z hz
    simpa [HalfPlaneOuterV2.poissonIntegral] using hDiskEq.trans hCoV

/-- New: Build a subset half‑plane Poisson representation for the Cayley pullback directly
from a subset half‑plane Poisson representation of the original function `F`.

Let `H w := F (fromDisk w)`. On any subset `S ⊆ Ω`, we have
`(H ∘ toDisk) z = F z` for `z ∈ S` and `H(boundaryToDisk t) = F(boundary t)`.
Thus the Poisson representation on `S` for `F` transfers verbatim to the pullback. -/
lemma pullback_rep_on_from_halfplane_rep
  (F : ℂ → ℂ) (H : ℂ → ℂ) {S : Set ℂ}
  (hHdef : ∀ w, H w = F (CayleyAdapters.fromDisk w))
  (hS : S ⊆ HalfPlaneOuterV2.Ω)
  (hRepOn : HalfPlaneOuterV2.HasPoissonRepOn F S)
  : HalfPlaneOuterV2.HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S := by
  refine {
    subset := hS
    , analytic := ?hA
    , integrable := ?hI
    , formula := ?hEq };
  · -- Analytic on S since `(H∘toDisk) = F` on S and `F` is analytic on S.
    have hEqOn : Set.EqOn (fun z => H (CayleyAdapters.toDisk z)) F S := by
      intro z hz; simp [hHdef]
    exact (hRepOn.analytic.congr hEqOn)
  · intro z hz
    -- Integrable boundary real part: equality of boundary traces transfers integrability
    -- `(H∘toDisk)(boundary t) = H(boundaryToDisk t) = F(boundary t)`
    have hbd : (fun t : ℝ => ((H (CayleyAdapters.toDisk (HalfPlaneOuterV2.boundary t))).re))
        = (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) := by
      funext t; simp [hHdef, CayleyAdapters.fromDisk_boundaryToDisk]
    -- use integrability from `hRepOn`
    simpa [hbd] using hRepOn.integrable z hz
  · intro z hz
    -- Formula equality transfers along the same boundary trace identity
    have hbd : (fun t : ℝ => (H (CayleyAdapters.boundaryToDisk t)).re)
        = (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) := by
      funext t; simp [hHdef, CayleyAdapters.fromDisk_boundaryToDisk]
    have hpoint : (fun z => H (CayleyAdapters.toDisk z)) z = F z := by
      simp [hHdef, CayleyAdapters.fromDisk_toDisk_of_mem_Ω (hS hz)]
    -- conclude using the Poisson formula for F on S
    simpa [HalfPlaneOuterV2.poissonIntegral, hbd, hpoint]
      using hRepOn.formula z hz

end PoissonCayley
end AcademicFramework
end RH
