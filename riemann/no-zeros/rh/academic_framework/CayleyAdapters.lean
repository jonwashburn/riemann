import rh.academic_framework.DiskHardy
import rh.academic_framework.HalfPlaneOuterV2
import Mathlib.Analysis.Analytic.Basic

noncomputable section

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Inverse Cayley map from the unit disk to the right half-plane Ω. -/
@[simp] def fromDisk (w : ℂ) : ℂ := 1 / (1 - w)

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuterV2.boundary t)

/-- Points of Ω are nonzero: if `Re z > 1/2` then `z ≠ 0`. -/
lemma memΩ_ne_zero {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) : z ≠ 0 := by
  intro h0
  have hzRe : (1/2 : ℝ) < z.re := by
    simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hz
  -- This would imply (1/2) < 0, a contradiction
  have hlt : (1/2 : ℝ) < 0 := by simpa [h0, Complex.zero_re] using hzRe
  exact (not_lt.mpr (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ))) hlt

/-- `toDisk` is analytic on Ω. -/
lemma toDisk_analyticOn_Ω : AnalyticOn ℂ toDisk HalfPlaneOuterV2.Ω := by
  -- toDisk z = (z - 1) / z is analytic on Ω (denominator nonzero on Ω)
  have h_id : AnalyticOn ℂ (fun z : ℂ => z) HalfPlaneOuterV2.Ω := analyticOn_id
  have h_const : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) HalfPlaneOuterV2.Ω := analyticOn_const
  have h_sub : AnalyticOn ℂ (fun z : ℂ => z - (1 : ℂ)) HalfPlaneOuterV2.Ω := h_id.sub h_const
  have h_div : AnalyticOn ℂ (fun z : ℂ => (z - 1) / z) HalfPlaneOuterV2.Ω :=
    h_sub.div h_id (by intro z hz; exact memΩ_ne_zero hz)
  simpa [toDisk] using h_div

/-- Algebraic identity: for any nonzero `z`, `fromDisk (toDisk z) = z`. -/
lemma fromDisk_toDisk_of_ne {z : ℂ} (hz : z ≠ 0) : fromDisk (toDisk z) = z := by
  -- fromDisk (toDisk z) = 1 / (1 - (z - 1) / z) = z, using `z ≠ 0`
  have h1 : (1 : ℂ) - (z - 1) / z = (1 : ℂ) / z := by
    field_simp [toDisk, hz]
  calc
    fromDisk (toDisk z)
        = 1 / (1 - (z - 1) / z) := by simp [fromDisk, toDisk]
    _ = 1 / ((1 : ℂ) / z) := by simpa [h1]
    _ = z := by field_simp [hz]

/-- Specialization on Ω: `fromDisk (toDisk z) = z`. -/
lemma fromDisk_toDisk_of_mem_Ω {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) :
    fromDisk (toDisk z) = z :=
  fromDisk_toDisk_of_ne (memΩ_ne_zero hz)

/-- Boundary points are nonzero. -/
lemma boundary_ne_zero (t : ℝ) : HalfPlaneOuterV2.boundary t ≠ 0 := by
  intro h0
  -- Get real-part = 0 from equality to 0
  have hRe0 : (HalfPlaneOuterV2.boundary t).re = 0 := by
    simpa using congrArg Complex.re h0
  -- But `(boundary t).re = 1/2`, contradiction
  have : (1/2 : ℝ) = 0 := by
    simpa [HalfPlaneOuterV2.boundary_re] using hRe0
  exact (by norm_num : (1/2 : ℝ) ≠ 0) this

/-- Boundary transport identity: `fromDisk (boundaryToDisk t) = boundary t`. -/
lemma fromDisk_boundaryToDisk (t : ℝ) :
    fromDisk (boundaryToDisk t) = HalfPlaneOuterV2.boundary t := by
  -- boundaryToDisk t = toDisk (boundary t)
  simpa [boundaryToDisk] using fromDisk_toDisk_of_ne (boundary_ne_zero t)

/-- Helper: rewrite `(1 - toDisk z)⁻¹` to `z` without unfolding in goals. -/
@[simp] lemma inv_one_sub_toDisk_of_ne {z : ℂ} (hz : z ≠ 0) :
    (1 - toDisk z)⁻¹ = z := by
  have h := fromDisk_toDisk_of_ne hz
  simpa [fromDisk] using h

/-- Helper: rewrite `(1 - boundaryToDisk t)⁻¹` to `boundary t`. -/
@[simp] lemma inv_one_sub_boundaryToDisk (t : ℝ) :
    (1 - boundaryToDisk t)⁻¹ = HalfPlaneOuterV2.boundary t := by
  have h := fromDisk_boundaryToDisk t
  simpa [fromDisk] using h

/-- From disk representation to subset half-plane representation for the pullback `H ∘ toDisk`. -/
@[simp] theorem pullback_rep_on_from_halfplane_rep
  (F : ℂ → ℂ) (H : ℂ → ℂ) {S : Set ℂ}
  (hHdef : ∀ w, H w = F (fromDisk w))
  (hS : S ⊆ HalfPlaneOuterV2.Ω)
  (hRepOn : HalfPlaneOuterV2.HasPoissonRepOn F S)
  : HalfPlaneOuterV2.HasPoissonRepOn (fun z => H (toDisk z)) S := by
  refine {
    subset := hS
    , analytic := ?hA
    , integrable := ?hI
    , formula := ?hEq };
  · -- Analytic on S since `(H∘toDisk) = F` on S and `F` is analytic on S.
    have hEqOn : Set.EqOn (fun z => H (toDisk z)) F S := by
      intro z hz
      have h1 := hHdef (toDisk z)
      have h1' := h1
      rw [fromDisk_toDisk_of_mem_Ω (hS hz)] at h1'
      exact h1'
    exact (hRepOn.analytic.congr hEqOn)
  · intro z hz
    -- Integrable boundary real part: match integrands pointwise and reuse `hRepOn.integrable`.
    have hIntF := hRepOn.integrable z hz
    -- Boundary real-part equality under Cayley
    have hbdRe_to : ∀ t : ℝ,
        (H (toDisk (HalfPlaneOuterV2.boundary t))).re = (F (HalfPlaneOuterV2.boundary t)).re := by
      intro t
      have h1 := hHdef (boundaryToDisk t)
      have h1' := h1
      rw [fromDisk_boundaryToDisk t] at h1'
      have hRe := congrArg Complex.re h1'
      simpa [boundaryToDisk] using hRe
    -- pointwise equality of the exact integrand shape
    have hEqFun :
        (fun t : ℝ =>
          (H (toDisk (HalfPlaneOuterV2.boundary t))).re * HalfPlaneOuterV2.poissonKernel z t)
        = (fun t : ℝ =>
          (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t) := by
      funext t
      -- multiply the boundary real-part equality by the kernel
      have := congrArg (fun r => r * HalfPlaneOuterV2.poissonKernel z t) (hbdRe_to t)
      simpa using this
    -- conclude by rewriting the integrand
    exact (hEqFun ▸ hIntF)
  · intro z hz
    -- Pointwise interior equality of real parts via `fromDisk ∘ toDisk = id`
    have hpointRe : (H (toDisk z)).re = (F z).re := by
      have h1 := hHdef (toDisk z)
      have h1' := h1
      rw [fromDisk_toDisk_of_mem_Ω (hS hz)] at h1'
      simpa using congrArg Complex.re h1'
    -- Boundary equality (real parts) under Cayley
    have hbdRe_to : ∀ t : ℝ,
        (H (toDisk (HalfPlaneOuterV2.boundary t))).re = (F (HalfPlaneOuterV2.boundary t)).re := by
      intro t
      have h1 := hHdef (boundaryToDisk t)
      have h1' := h1
      rw [fromDisk_boundaryToDisk t] at h1'
      have hRe := congrArg Complex.re h1'
      simpa [boundaryToDisk] using hRe
    -- rewrite the Poisson integral's integrand by equality of boundary traces
    have hUeq : (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re)
            = (fun t : ℝ => (H (toDisk (HalfPlaneOuterV2.boundary t))).re) := by
      funext t; simpa using (hbdRe_to t).symm
    -- Finish (rewrite to F-side Poisson, then to H-side by hUeq)
    have hFPI : (F z).re
        = HalfPlaneOuterV2.poissonIntegral (fun t => (F (HalfPlaneOuterV2.boundary t)).re) z :=
      hRepOn.formula z hz
    have hHPI1 : (H (toDisk z)).re
        = HalfPlaneOuterV2.poissonIntegral (fun t => (F (HalfPlaneOuterV2.boundary t)).re) z := by
      simpa [hFPI] using hpointRe
    -- Rewrite equality of Poisson integrals by transporting equality of integrands
    have hEqFunInt :
        (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t)
        = (fun t : ℝ => (H (toDisk (HalfPlaneOuterV2.boundary t))).re * HalfPlaneOuterV2.poissonKernel z t) := by
      funext t
      -- Multiply the pointwise boundary real-part equality by the kernel
      exact congrArg (fun r : ℝ => r * HalfPlaneOuterV2.poissonKernel z t) ((hbdRe_to t).symm)
    have hSwap :
        HalfPlaneOuterV2.poissonIntegral (fun t => (F (HalfPlaneOuterV2.boundary t)).re) z
        = HalfPlaneOuterV2.poissonIntegral (fun t => (H (toDisk (HalfPlaneOuterV2.boundary t))).re) z := by
      classical
      dsimp [HalfPlaneOuterV2.poissonIntegral]
      exact congrArg (fun f => ∫ t, f t) hEqFunInt
    exact hHPI1.trans hSwap

end CayleyAdapters
end AcademicFramework
end RH
