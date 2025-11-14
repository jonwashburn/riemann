import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.PoissonCayley
import rh.academic_framework.CayleyAdapters

/-!
# Poisson AI helpers

This module records small helper lemmas for bridging the Cayley pullback
representation to the θ‑free Poisson real-part identity on `offXi`.  The goal
is to keep the machinery available to Route B while avoiding heavy imports.
-/

noncomputable section

namespace RH
namespace RS
namespace PoissonAI

open Complex Set MeasureTheory
open RH.AcademicFramework
open RH.AcademicFramework.HalfPlaneOuterV2
open RH.AcademicFramework.PoissonCayley
open RH.AcademicFramework.CayleyAdapters
open scoped MeasureTheory

/-- Boundary parametrisation of the critical line. -/
@[simp] def boundaryMap (t : ℝ) : ℂ := (1/2 : ℂ) + Complex.I * (t : ℂ)

/-- Boundary real part helper used by the classical AI statements. -/
@[simp] def boundaryRe (F : ℂ → ℂ) (t : ℝ) : ℝ := (F (boundaryMap t)).re

/-- Half-plane Poisson kernel (classical normalisation). -/
@[simp] def poissonKernel (b x : ℝ) : ℝ := b / (Real.pi * (b^2 + x^2))

/-- Smoothed boundary trace used in the AI statements. -/
@[simp] def poissonSmooth (F : ℂ → ℂ) (b x : ℝ) : ℝ :=
  ∫ t, poissonKernel b (x - t) * boundaryRe F t ∂(volume)

/-
  ## θ‑free Cayley bridge
-/

section ThetaFree

variable {det2 O : ℂ → ℂ}

/-- Canonical Cayley pullback for the pinch field. -/
def H_pinch (det2 O : ℂ → ℂ) (w : ℂ) : ℂ :=
  F_pinch det2 O (fromDisk w)

@[simp] lemma H_pinch_def (det2 O : ℂ → ℂ) :
    ∀ w, H_pinch det2 O w = F_pinch det2 O (fromDisk w) := by
  intro w; rfl

/-- Interior equality on `offXi`: `F(z) = H_pinch (toDisk z)`. -/
lemma hEqInterior_pinch
  (det2 O : ℂ → ℂ) :
  Set.EqOn (F_pinch det2 O)
    (fun z => H_pinch det2 O (toDisk z)) offXi := by
  intro z hz
  have hzΩ : z ∈ Ω := offXi_subset_Ω hz
  have h := map_fromDisk_toDisk (F := fun u => F_pinch det2 O u) hzΩ
  simpa [H_pinch] using h.symm

/-- Boundary alignment: `F(boundary t) = H_pinch(boundaryToDisk t)` on ℝ. -/
lemma hEqBoundary_pinch (det2 O : ℂ → ℂ) :
  EqOnBoundary (F_pinch det2 O) (H_pinch det2 O) := by
  intro t
  have h := map_fromDisk_boundaryToDisk (F := fun u => F_pinch det2 O u) t
  simpa [EqOnBoundary, H_pinch] using h.symm

/-- θ‑free real-part identity on `offXi` from a pullback Poisson representation. -/
theorem thetaFree_hReEqOn_offXi_from_pullback
  (det2 O : ℂ → ℂ)
  (hRepPull : HasPoissonRepOn (fun z => H_pinch det2 O (toDisk z)) offXi) :
  HasHalfPlanePoissonReEqOn (F_pinch det2 O) offXi := by
  have hInt := hEqInterior_pinch (det2 := det2) (O := O)
  have hBd := hEqBoundary_pinch (det2 := det2) (O := O)
  exact pinch_theta_free_ReEqOn_offXi
    (det2 := det2) (O := O) (H := H_pinch det2 O)
    (hEqInt := hInt) (hEqBd := hBd) (hRepPull := hRepPull)

end ThetaFree

end PoissonAI
end RS
end RH
