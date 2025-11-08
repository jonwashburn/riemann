import Mathlib.Analysis.Analytic.Basic
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CayleyAdapters
-- keep this module AF-only to avoid RS build dependencies
import Mathlib.MeasureTheory.Integral.Bochner

-- Poisson–Cayley (θ‑free): minimal Route B bridge from disk to half‑plane.
-- Public API: `HasHalfPlanePoissonReEqOn`, `EqOnBoundary`, `CayleyKernelTransportOn`,
-- `reEq_on_from_disk_via_cayley`, `cayley_kernel_transport_from_rep_on`,
-- `pinch_halfplane_ReEqOn_from_cayley`, `pinch_ReEqOn_from_pullback`,
-- and the re-export `pullback_rep_on_from_halfplane_rep`.
-- No θ, and no `axiom`/`admit`/`sorry`. AF-only to avoid RS deps.

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

/-- Poisson real‑part identity for `F` on a subset `S ⊆ Ω`. -/
def HasHalfPlanePoissonReEqOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, (F z).re = poissonIntegral (fun t : ℝ => (F (boundary t)).re) z

-- ext specialization removed: keep θ‑free minimal API

-- Once the real‑part identity is available on `S`, the subset Poisson
-- representation used by the pinch route follows via
-- `HalfPlaneOuterV2.pinch_poissonRepOn_offZeros`. The packagers below
-- expose this step explicitly for readability.

-- (trimmed)

/-- Boundary identification along Cayley: `F ∘ boundary = H ∘ boundaryToDisk`. -/
def EqOnBoundary (F H : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, F (boundary t) = H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)

/-- Cayley kernel transport on `S`: Poisson of pullback boundary real part equals `(H ∘ toDisk).re`. -/
def CayleyKernelTransportOn (H : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
      = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re

-- Private congruence helper: rewrite a Poisson integral from equality of boundary real‑part maps.
private lemma poissonIntegral_congr_boundary_re
  (F H : ℂ → ℂ) (z : ℂ)
  (h : (fun t : ℝ => (F (boundary t)).re)
        = (fun t : ℝ => (H (CayleyAdapters.boundaryToDisk t)).re))
  : poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
      = poissonIntegral (fun t : ℝ => (H (CayleyAdapters.boundaryToDisk t)).re) z := by
  exact congrArg (fun u => poissonIntegral u z) h

/-- Half‑plane real‑part identity on `S` from interior/boundary matches and kernel transport. -/
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
          = poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z :=
            poissonIntegral_congr_boundary_re F H z hIntgEq
      _ = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re :=
            hKernel z hzS
  -- finish with interior identification of real parts
  simpa [h1] using hPI.symm

-- Boundary identity for the Cayley pullback: `F(boundary t) = H(boundaryToDisk t)`.

/-! A direct bridge: a subset half‑plane Poisson representation immediately yields
the real‑part identity on that subset. This is used to convert witnesses when
assembling the Cayley transport pipeline. -/
theorem hReEq_on_of_halfplane_rep_on (F : ℂ → ℂ) {S : Set ℂ}
  (hRepOn : HasPoissonRepOn F S) : HasHalfPlanePoissonReEqOn F S := by
  intro z hz
  exact hRepOn.formula z hz

/-- Kernel transport on `S` for `H` from a Poisson rep of `(H ∘ toDisk)`. -/
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

-- The remaining pinch-specialized and pullback representation sections are omitted
-- to keep this module minimal and compiling.

-- Global bridge: from a half-plane Poisson representation of `F`, obtain the
-- real-part identity on all of Ω.
-- (removed: not used by Route B)

-- Subset bridge: from a subset half-plane Poisson representation of `F` on `S`,
-- obtain the real-part identity on `S`.
-- (removed: not used by Route B)

-- Pinch specialization (ext): if the pinch field admits a half-plane Poisson
-- representation on Ω, then the real-part identity holds on the off-zeros subset `S`.
-- (removed ext specialization: symbol deleted)

-- Pinch specialization via Cayley: transport through the Cayley bridge.

/-- Builder: with `hEqInterior`, `hEqBoundary`, and rep of `(H ∘ toDisk)`, get Re‑Eq on `S`. -/
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

/-- From a subset Poisson rep of `(F_pinch det2 O) ∘ toDisk` on `S`, get Re‑Eq on `S`. -/
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

  -- θ-based sections removed: θ-free API suffices for Route B

/-- θ‑free identity (wrapper): given interior and boundary identifications via Cayley
and a subset Poisson representation for the pullback `(H ∘ toDisk)` on `offXi`,
conclude the half‑plane real‑part identity for the pinch field on `offXi`. -/
theorem pinch_theta_free_ReEqOn_offXi
  (det2 O H : ℂ → ℂ)
  (hEqInt : Set.EqOn (HalfPlaneOuterV2.F_pinch det2 O)
              (fun z => H (CayleyAdapters.toDisk z)) HalfPlaneOuterV2.offXi)
  (hEqBd  : EqOnBoundary (HalfPlaneOuterV2.F_pinch det2 O) H)
  (hRepPull : HalfPlaneOuterV2.HasPoissonRepOn
                (fun z => H (CayleyAdapters.toDisk z)) HalfPlaneOuterV2.offXi)
  : HasHalfPlanePoissonReEqOn (HalfPlaneOuterV2.F_pinch det2 O) HalfPlaneOuterV2.offXi := by
  -- specialize the generic builder to `S = offXi`
  exact pinch_ReEqOn_from_pullback (det2 := det2) (O := O)
    (S := HalfPlaneOuterV2.offXi) (H := H) hEqInt hEqBd hRepPull

/-- Subset Poisson rep for `H ∘ toDisk` on `S` from a rep of `F` on `S`. -/
theorem pullback_rep_on_from_halfplane_rep
  (F : ℂ → ℂ) (H : ℂ → ℂ) {S : Set ℂ}
  (hHdef : ∀ w, H w = F (CayleyAdapters.fromDisk w))
  (hS : S ⊆ HalfPlaneOuterV2.Ω)
  (hRepOn : HalfPlaneOuterV2.HasPoissonRepOn F S)
  : HalfPlaneOuterV2.HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S := by
  exact CayleyAdapters.pullback_rep_on_from_halfplane_rep F H hHdef hS hRepOn

end PoissonCayley

end AcademicFramework
end RH
