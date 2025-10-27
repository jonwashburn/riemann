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

/-- On the right half-plane Ω = {Re z > 1/2}, the Cayley maps cancel:
`fromDisk (toDisk z) = z`. This is the involutive identity restricted to Ω
(where the denominator is nonzero). -/
lemma fromDisk_toDisk_of_mem_Ω {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) :
    fromDisk (toDisk z) = z :=
  fromDisk_toDisk_of_ne (memΩ_ne_zero hz)

@[simp] lemma fromDisk_toDisk_simp {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) :
    fromDisk (toDisk z) = z := fromDisk_toDisk_of_mem_Ω hz

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

/-- Boundary transport under the Cayley map: on the line Re z = 1/2,
`fromDisk (boundaryToDisk t) = HalfPlaneOuterV2.boundary t`. -/
@[simp] lemma fromDisk_boundaryToDisk (t : ℝ) :
    fromDisk (boundaryToDisk t) = HalfPlaneOuterV2.boundary t := by
  -- boundaryToDisk t = toDisk (boundary t)
  simpa [boundaryToDisk] using fromDisk_toDisk_of_ne (boundary_ne_zero t)

/-- Rewrite lemma (safe for `simp`): for `z ≠ 0`, `(1 - toDisk z)⁻¹ = z`. -/
@[simp] lemma inv_one_sub_toDisk_of_ne {z : ℂ} (hz : z ≠ 0) :
    (1 - toDisk z)⁻¹ = z := by
  have h := fromDisk_toDisk_of_ne hz
  simpa [fromDisk] using h

/-- Boundary rewrite (safe for `simp`):
`(1 - boundaryToDisk t)⁻¹ = HalfPlaneOuterV2.boundary t`. -/
@[simp] lemma inv_one_sub_boundaryToDisk (t : ℝ) :
    (1 - boundaryToDisk t)⁻¹ = HalfPlaneOuterV2.boundary t := by
  have h := fromDisk_boundaryToDisk t
  simpa [fromDisk] using h

-- Helper simp for rewriting under arbitrary maps (used implicitly by `simp`).
@[simp] lemma map_fromDisk_toDisk
    {α : Sort _} (F : ℂ → α) {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) :
    F (fromDisk (toDisk z)) = F z := by
  simpa using congrArg F (fromDisk_toDisk_of_mem_Ω hz)

@[simp] lemma map_fromDisk_boundaryToDisk
    {α : Sort _} (F : ℂ → α) (t : ℝ) :
    F (fromDisk (boundaryToDisk t)) = F (HalfPlaneOuterV2.boundary t) := by
  simpa using congrArg F (fromDisk_boundaryToDisk t)

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
      -- `H (toDisk z) = F (fromDisk (toDisk z))`, then `fromDisk ∘ toDisk = id` on Ω
      simpa only [fromDisk_toDisk_of_mem_Ω (hS hz)] using hHdef (toDisk z)
    exact (hRepOn.analytic.congr hEqOn)
  · intro z hz
    -- Integrable boundary real part: match integrands pointwise and reuse `hRepOn.integrable`.
    have hIntF := hRepOn.integrable z hz
    -- Boundary real-part equality under Cayley
    have hbdRe_to : ∀ t : ℝ,
        (H (toDisk (HalfPlaneOuterV2.boundary t))).re = (F (HalfPlaneOuterV2.boundary t)).re := by
      intro t
      -- take real parts of `H (boundaryToDisk t) = F (fromDisk (boundaryToDisk t))`
      have h := congrArg Complex.re (hHdef (boundaryToDisk t))
      have h' : (H (toDisk (HalfPlaneOuterV2.boundary t))).re
          = (F (fromDisk (boundaryToDisk t))).re := by
        simpa [boundaryToDisk] using h
      have hF : (F (fromDisk (boundaryToDisk t))).re
          = (F (HalfPlaneOuterV2.boundary t)).re := by
        simpa using congrArg Complex.re (map_fromDisk_boundaryToDisk F t)
      exact h'.trans hF
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
      -- take real parts of `H (toDisk z) = F (fromDisk (toDisk z))` and simplify
      simpa only [fromDisk_toDisk_of_mem_Ω (hS hz)] using
        congrArg Complex.re (hHdef (toDisk z))
    -- Boundary equality (real parts) under Cayley
    have hbdRe_to : ∀ t : ℝ,
        (H (toDisk (HalfPlaneOuterV2.boundary t))).re = (F (HalfPlaneOuterV2.boundary t)).re := by
      intro t
      have h := congrArg Complex.re (hHdef (boundaryToDisk t))
      have h' : (H (toDisk (HalfPlaneOuterV2.boundary t))).re
          = (F (fromDisk (boundaryToDisk t))).re := by
        simpa [boundaryToDisk] using h
      have hF : (F (fromDisk (boundaryToDisk t))).re
          = (F (HalfPlaneOuterV2.boundary t)).re := by
        simpa using congrArg Complex.re (map_fromDisk_boundaryToDisk F t)
      exact h'.trans hF
    -- rewrite the Poisson integral's integrand by equality of boundary traces
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
