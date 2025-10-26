import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Academic holder: disk-level Hardy/Smirnov interfaces used by the Cayley route.
We record the unit disk, boundary parametrization, a disk Poisson kernel, and a
statement-level Poisson representation structure for the unit disk. RS/AF layers
consume these via the Cayley adapters.
-/
noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace RH
namespace AcademicFramework
namespace DiskHardy

/- Unit disk set. -/
def unitDisk : Set ℂ := { z : ℂ | ‖z‖ < 1 }

/- Boundary parametrization of ∂𝔻: e^{iθ}. -/
@[simp] def boundary (θ : ℝ) : ℂ := Complex.exp (Complex.I * θ)

/-- Disk Poisson kernel (normalized by 2π):
  P(z, e^{iθ}) = (1 - |z|^2) / |e^{iθ} - z|^2 · (1 / (2π)). -/
@[simp] def poissonKernel (z : ℂ) (θ : ℝ) : ℝ :=
  let num : ℝ := 1 - ‖z‖^2
  let den : ℝ := (Complex.abs (boundary θ - z))^2
  (num / den) * (1 / (2 * Real.pi))

/-- Prop-level: Poisson/Herglotz representation on the unit disk for the real part. -/
structure HasDiskPoissonRepresentation (F : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ F unitDisk)
  (integrable : ∀ z ∈ unitDisk, Integrable (fun θ : ℝ => (F (boundary θ)).re * poissonKernel z θ))
  (re_eq : ∀ z ∈ unitDisk, (F z).re = ∫ θ : ℝ, (F (boundary θ)).re * poissonKernel z θ)

/-! Minimal packaging: build a disk Poisson representation from supplied data. -/
/-- Packaging constructor: build a disk Poisson representation from supplied data. -/
lemma HasDiskPoissonRepresentation_of_data
  {F : ℂ → ℂ}
  (hA : AnalyticOn ℂ F unitDisk)
  (hI : ∀ z ∈ unitDisk, Integrable (fun θ : ℝ => (F (boundary θ)).re * poissonKernel z θ))
  (hEq : ∀ z ∈ unitDisk, (F z).re = ∫ θ : ℝ, (F (boundary θ)).re * poissonKernel z θ)
  : HasDiskPoissonRepresentation F :=
{ analytic := hA, integrable := hI, re_eq := hEq }

/-- Minimal disk Poisson representation (real-part variant).
Given analytic F on 𝔻, if the boundary real part u(θ) := Re F(e^{iθ}) is locally integrable
and uniformly bounded by M on the circle, then Re F(z) is represented by the Poisson integral
against u for all z ∈ 𝔻. We package as a `HasDiskPoissonRepresentation`.

This lemma is a statement-level constructor expecting the integrability and identity to be
provided by callers (e.g. via standard facts); it simply packages them.
-/
lemma HasDiskPoissonRepresentation_real
  {F : ℂ → ℂ}
  (hA : AnalyticOn ℂ F unitDisk)
  (hI : ∀ z ∈ unitDisk, Integrable (fun θ : ℝ => (F (boundary θ)).re * poissonKernel z θ))
  (hEq : ∀ z ∈ unitDisk, (F z).re = ∫ θ : ℝ, (F (boundary θ)).re * poissonKernel z θ)
  : HasDiskPoissonRepresentation F :=
HasDiskPoissonRepresentation_of_data (F := F) hA hI hEq

end DiskHardy
end AcademicFramework
end RH
