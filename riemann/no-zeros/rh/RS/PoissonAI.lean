import rh.academic_framework.PoissonCayley

/-!
# Poisson AI helpers (deprecated)

The original θ-free Cayley bridge now lives in `rh/academic_framework/PoissonCayley`.
This module re-exports the historical `RH.RS.PoissonAI` namespace for compatibility.
-/

noncomputable section

namespace RH
namespace RS
namespace PoissonAI

open RH.AcademicFramework
open RH.AcademicFramework.CayleyAdapters
open RH.AcademicFramework.HalfPlaneOuterV2

abbrev H_pinch (det2 O : ℂ → ℂ) :=
  RH.AcademicFramework.PoissonCayley.H_pinch det2 O

@[simp] lemma H_pinch_def (det2 O : ℂ → ℂ) :
    ∀ w, H_pinch det2 O w = F_pinch det2 O (fromDisk w) := by
  intro w
  simpa [H_pinch] using
    RH.AcademicFramework.PoissonCayley.H_pinch_def (g := det2) (O := O) w

lemma hEqInterior_pinch
  (det2 O : ℂ → ℂ) :
  Set.EqOn (F_pinch det2 O)
    (fun z => H_pinch det2 O (toDisk z)) offXi := by
  simpa [H_pinch] using
    RH.AcademicFramework.PoissonCayley.hEqInterior_pinch (g := det2) (O := O)

lemma hEqBoundary_pinch (det2 O : ℂ → ℂ) :
  RH.AcademicFramework.PoissonCayley.EqOnBoundary (F_pinch det2 O) (H_pinch det2 O) := by
  simpa [H_pinch] using
    RH.AcademicFramework.PoissonCayley.hEqBoundary_pinch (g := det2) (O := O)

theorem thetaFree_hReEqOn_offXi_from_pullback
  (det2 O : ℂ → ℂ)
  (hRepPull : HasPoissonRepOn (fun z => H_pinch det2 O (toDisk z)) offXi) :
  RH.AcademicFramework.PoissonCayley.HasHalfPlanePoissonReEqOn
    (F_pinch det2 O) offXi := by
  simpa [H_pinch] using
    RH.AcademicFramework.PoissonCayley.thetaFree_hReEqOn_offXi_from_pullback
      (g := det2) (O := O) hRepPull

end PoissonAI
end RS
end RH
