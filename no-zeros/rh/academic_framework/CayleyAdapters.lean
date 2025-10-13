import rh.academic_framework.DiskHardy
-- (no additional mathlib imports needed here)
import rh.academic_framework.HalfPlaneOuterV2
import Mathlib.Tactic

noncomputable section

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework
open scoped Real

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Inverse Cayley map from the unit disk to the right half-plane Ω. -/
@[simp] def toHalf (w : ℂ) : ℂ := 1 / (1 - w)

/-- Inverse adapter name used by RS routing: identical to `toHalf`. -/
@[simp] def fromDisk (w : ℂ) : ℂ := toHalf w

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuterV2.boundary t)

/-! ## Geometry facts for the Cayley transform -/

-- Absolute value of `toDisk z` as the ratio `|z−1|/|z|` (valid for `z ≠ 0`).
lemma abs_toDisk (z : ℂ) (hz : z ≠ 0) :
  Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z := by
  -- prefer `abs_div` over `Complex.abs_div`
  simpa [toDisk, hz] using abs_div (z - 1) z

-- The boundary point `s = 1/2 + i t` is never zero.
lemma boundary_ne_zero (t : ℝ) : HalfPlaneOuterV2.boundary t ≠ 0 := by
  -- Show the real part is nonzero, so the complex number is nonzero
  intro h
  have hRe_ne : (HalfPlaneOuterV2.boundary t).re ≠ 0 := by
    -- (boundary t).re = 1/2 ≠ 0
    have : (1/2 : ℝ) ≠ 0 := by norm_num
    simpa [HalfPlaneOuterV2.boundary_mk_eq] using this
  -- But equality to 0 forces real part to be 0
  have hRe0 : (HalfPlaneOuterV2.boundary t).re = 0 := by
    simpa using congrArg Complex.re h
  exact hRe_ne hRe0

lemma map_Ω_to_unitDisk {z : ℂ}
  (hz : z ∈ HalfPlaneOuterV2.Ω) : toDisk z ∈ DiskHardy.unitDisk := by
  -- Re z > 1/2 ⇒ |z-1| < |z| ⇒ |(z-1)/z| < 1
  have hzRe : (1/2 : ℝ) < z.re := by simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hz
  have hzNe : z ≠ 0 := by
    intro h; subst h; simp at hzRe; linarith
  have hsq : (Complex.abs (z - 1))^2 = (Complex.abs z)^2 - 2 * z.re + 1 := by
    simp [Complex.sq_abs, Complex.normSq_sub, Complex.normSq_one]
    ring
  have hlt : Complex.abs (z - 1) < Complex.abs z := by
    -- Compare squares using Re z > 1/2, then drop squares on nonnegative reals
    have hlt_sq : (Complex.abs (z - 1))^2 < (Complex.abs z)^2 := by
      rw [hsq]
      have : - 2 * z.re + 1 < 0 := by linarith
      linarith
    -- Convert a^2 < b^2 to a < b using sq_lt_sq on ℝ
    have habs_lt : |Complex.abs (z - 1)| < |Complex.abs z| := (sq_lt_sq).1 hlt_sq
    simpa using habs_lt
  have : Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z := by
    -- directly by abs_div
    have : Complex.abs ((z - 1) / z) = Complex.abs (z - 1) / Complex.abs z := by
      simpa using abs_div (z - 1) z
    simpa [toDisk, hzNe] using this
  have hlt' : Complex.abs (toDisk z) < 1 := by
    rw [this]
    have hzpos : 0 < Complex.abs z := AbsoluteValue.pos Complex.abs hzNe
    exact div_lt_one hzpos |>.mpr hlt
  simpa [DiskHardy.unitDisk, Set.mem_setOf_eq] using hlt'

/-! ## Two‑sided inverse identities for Cayley (domain‑restricted) -/

/-- On the unit disk (|w| < 1), `toDisk ∘ fromDisk = id`. -/
lemma toDisk_fromDisk_of_mem_unitDisk {w : ℂ}
  (hw : w ∈ DiskHardy.unitDisk) : toDisk (fromDisk w) = w := by
  -- Since |w| < 1, we have w ≠ 1, hence 1 - w ≠ 0
  have hw_lt : Complex.abs w < 1 := by
    simpa [DiskHardy.unitDisk, Set.mem_setOf_eq] using hw
  have h1w : 1 - w ≠ 0 := by
    intro h
    have hw_eq : w = (1 : ℂ) := (eq_of_sub_eq_zero h).symm
    have : Complex.abs (1 : ℂ) < 1 := by simpa [hw_eq] using hw_lt
    have : (1 : ℝ) < 1 := by simpa [abs_one] using this
    exact (lt_irrefl (1 : ℝ)) this
  -- Compute directly
  field_simp [fromDisk, toHalf, toDisk, h1w]

/-- On the right half‑plane Ω (Re z > 1/2), `fromDisk ∘ toDisk = id`. -/
lemma fromDisk_toDisk_of_ne_zero {z : ℂ}
  (hz : z ≠ 0) : fromDisk (toDisk z) = z := by
  field_simp [fromDisk, toHalf, toDisk, hz]

lemma fromDisk_toDisk_of_mem_Ω {z : ℂ}
  (hz : z ∈ HalfPlaneOuterV2.Ω) : fromDisk (toDisk z) = z := by
  have hz0 : z ≠ 0 := by
    intro h; subst h
    have : (1/2 : ℝ) < (0 : ℂ).re := by
      simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hz
    have : (1/2 : ℝ) < 0 := by simpa [Complex.zero_re] using this
    exact (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 1/2)) this
  exact fromDisk_toDisk_of_ne_zero hz0

/-- Boundary compatibility: pulling boundary points back from the disk recovers the boundary. -/
@[simp] lemma fromDisk_boundaryToDisk (t : ℝ) :
  fromDisk (boundaryToDisk t) = HalfPlaneOuterV2.boundary t := by
  have hb0 : HalfPlaneOuterV2.boundary t ≠ 0 := boundary_ne_zero t
  -- Apply the general inverse identity valid for all nonzero points
  simpa [boundaryToDisk] using fromDisk_toDisk_of_ne_zero (z := HalfPlaneOuterV2.boundary t) hb0

-- Note: the boundary image lies on the unit circle; not required downstream here.
-- lemma boundary_maps_to_unitCircle (t : ℝ) : Complex.abs (boundaryToDisk t) = 1 := by
--   -- Proof available via direct algebra on abs-squared; omitted since unused.
--   admit

/-!
## Change-of-variables helpers for Cayley

We record algebraic identities used in the half‑plane↔disk Poisson kernel
change‑of‑variables calculation.
-/

open Complex

-- Closed form for `boundaryToDisk t` as a rational expression in `t` (omitted).

-- (removed duplicate abs_toDisk lemma)

/-- `1 - ‖toDisk z‖^2` in terms of `z` (valid for `z ≠ 0`). -/
lemma one_minus_absSq_toDisk (z : ℂ) (hz : z ≠ 0) :
  1 - (Complex.abs (toDisk z))^2 =
    ((2 : ℝ) * z.re - 1) / (Complex.abs z)^2 := by
  have h : Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z :=
    abs_toDisk z hz
  -- 1 - (|z-1|/|z|)^2 = (|z|^2 - |z-1|^2) / |z|^2
  rw [h]
  have : 1 - (Complex.abs (z - 1) / Complex.abs z)^2
        = ((Complex.abs z)^2 - (Complex.abs (z - 1))^2) / (Complex.abs z)^2 := by
    have hz_ne : Complex.abs z ≠ 0 := AbsoluteValue.ne_zero Complex.abs hz
    field_simp [hz_ne]
  -- |z|^2 - |z-1|^2 = 2 Re z - 1
  have hdiff : (Complex.abs z)^2 - (Complex.abs (z - 1))^2
      = (2 : ℝ) * z.re - 1 := by
    -- Expand |z-1|^2 = |z|^2 - 2 Re z + 1
    rw [Complex.sq_abs, Complex.sq_abs, Complex.normSq_sub]
    simp [Complex.normSq_one]
    ring
  simp [this, hdiff]

-- (moved earlier)

/-- Difference of Cayley images in terms of original points. Requires both nonzero. -/
lemma toDisk_sub (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
  toDisk u - toDisk v = (u - v) / (u * v) := by
  -- toDisk w = 1 - 1/w
  simp [toDisk]
  field_simp [hu, hv]
  ring

/-- Absolute value of the boundary/disk difference in terms of original points. -/
lemma abs_boundaryToDisk_sub_toDisk (t : ℝ) (z : ℂ) (hz : z ≠ 0) :
  Complex.abs (boundaryToDisk t - toDisk z)
    = Complex.abs (HalfPlaneOuterV2.boundary t - z)
        / (Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z) := by
  have hs0 : HalfPlaneOuterV2.boundary t ≠ 0 := boundary_ne_zero t
  have hdiff : boundaryToDisk t - toDisk z
      = (HalfPlaneOuterV2.boundary t - z) / (HalfPlaneOuterV2.boundary t * z) := by
    -- use the general difference formula specialized to u=s, v=z
    have := toDisk_sub (HalfPlaneOuterV2.boundary t) z hs0 hz
    -- boundaryToDisk t = toDisk (boundary t)
    simpa [boundaryToDisk] using this
  -- take absolute values
  rw [hdiff]
  have hdiv : Complex.abs ((HalfPlaneOuterV2.boundary t - z) / (HalfPlaneOuterV2.boundary t * z))
      = Complex.abs (HalfPlaneOuterV2.boundary t - z)
          / Complex.abs (HalfPlaneOuterV2.boundary t * z) := by
    simpa using abs_div (HalfPlaneOuterV2.boundary t - z) (HalfPlaneOuterV2.boundary t * z)
  have hmul : Complex.abs (HalfPlaneOuterV2.boundary t * z)
      = Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z := by
    simpa using Complex.abs_mul (HalfPlaneOuterV2.boundary t) z
  simpa [hdiv, hmul]

/-- Core density identity: rewrite `(1 - |w|^2)/|ξ − w|^2` in half‑plane variables. -/
lemma density_ratio_boundary (z : ℂ) (hzΩ : z ∈ HalfPlaneOuterV2.Ω) (t : ℝ) :
  let w := toDisk z
  let ξ := boundaryToDisk t
  (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
    = ((2 : ℝ) * z.re - 1) * (Complex.abs (HalfPlaneOuterV2.boundary t))^2
        / (Complex.abs (HalfPlaneOuterV2.boundary t - z))^2 := by
  classical
  intro w ξ
  -- Abbreviation for the boundary point
  set s : ℂ := HalfPlaneOuterV2.boundary t with hs
  -- Nonvanishing of z and s
  have hz0 : z ≠ 0 := by
    intro hz; subst hz
    have hlt : (1 / 2 : ℝ) < (0 : ℝ) := by
      simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hzΩ
    have : ¬ ((1 / 2 : ℝ) < 0) := by norm_num
    exact (this hlt).elim
  have hs0 : s ≠ 0 := by
    simpa [hs] using boundary_ne_zero t
  -- Denominator equality from abs difference formula
  have hDen_abs :
      Complex.abs (ξ - w) = Complex.abs (s - z) / (Complex.abs s * Complex.abs z) := by
    simpa [ξ, w, hs] using abs_boundaryToDisk_sub_toDisk t z hz0
  -- Square both sides
  have hDen : Complex.abs (ξ - w) ^ 2
      = Complex.abs (s - z) ^ 2 / (Complex.abs s ^ 2 * Complex.abs z ^ 2) := by
    have h2 := congrArg (fun x : ℝ => x ^ 2) hDen_abs
    -- Use (a/b)^2 = a^2 / b^2 and |ab|^2 = |a|^2 |b|^2; avoid expanding x^2 to x*x
    simpa [div_pow, mul_pow] using h2
  -- Numerator identity
  have hNum : 1 - Complex.abs w ^ 2
      = ((2 : ℝ) * z.re - 1) / Complex.abs z ^ 2 := by
    simpa [w] using one_minus_absSq_toDisk z hz0
  -- Nonzero denominators for field_simp
  have hzabs_ne : Complex.abs z ^ 2 ≠ 0 := by
    have hzabs : Complex.abs z ≠ 0 := AbsoluteValue.ne_zero Complex.abs hz0
    exact pow_ne_zero 2 hzabs
  have hsabs_ne : Complex.abs s ^ 2 ≠ 0 := by
    have hsabs : Complex.abs s ≠ 0 := AbsoluteValue.ne_zero Complex.abs hs0
    exact pow_ne_zero 2 hsabs
  have hzRe : (1 / 2 : ℝ) < z.re := by
    simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hzΩ
  have hsminusz_ne : s - z ≠ 0 := by
    intro h
    have hRe0 : (s - z).re = 0 := by simpa using congrArg Complex.re h
    have : (s - z).re = (1 / 2 : ℝ) - z.re := by
      simp [hs, HalfPlaneOuterV2.boundary_re]
    have : (1 / 2 : ℝ) - z.re = 0 := by simpa [this] using hRe0
    have : (1 / 2 : ℝ) = z.re := by linarith
    exact (ne_of_gt hzRe) (by simpa using this.symm)
  have hsminusz_abs_ne : Complex.abs (s - z) ^ 2 ≠ 0 := by
    have : Complex.abs (s - z) ≠ 0 := AbsoluteValue.ne_zero Complex.abs hsminusz_ne
    exact pow_ne_zero 2 this
  -- Combine and simplify in one algebra step: ((A/B) / (C/(D*B))) = (A*D)/C
  have hRewrite :
    ((1 - Complex.abs w ^ 2) / Complex.abs (ξ - w) ^ 2)
      = (((2 : ℝ) * z.re - 1) / Complex.abs z ^ 2) /
          (Complex.abs (s - z) ^ 2 / (Complex.abs s ^ 2 * Complex.abs z ^ 2)) := by
    simpa [hNum, hDen]
  have hAlg :
    (((2 : ℝ) * z.re - 1) / Complex.abs z ^ 2) /
      (Complex.abs (s - z) ^ 2 / (Complex.abs s ^ 2 * Complex.abs z ^ 2))
    = (((2 : ℝ) * z.re - 1) * Complex.abs s ^ 2) / Complex.abs (s - z) ^ 2 := by
    field_simp [hzabs_ne, hsabs_ne, hsminusz_abs_ne, mul_comm, mul_left_comm, mul_assoc]
  simpa [hs] using hRewrite.trans hAlg

/-- Real parameters `a(z) = Re z − 1/2` and `b(z) = Im z` for change-of-variables. -/
def a (z : ℂ) : ℝ := z.re - (1/2 : ℝ)
def b (z : ℂ) : ℝ := z.im

lemma a_pos_of_mem_Ω {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) : 0 < a z := by
  simp only [a, HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] at hz ⊢
  linarith

-- (Angle parametrization lemmas omitted here; not needed for algebraic identities above.)

/-- Points of Ω are nonzero: if `Re z > 1/2` then `z ≠ 0`. -/
lemma memΩ_ne_zero {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) : z ≠ 0 := by
  intro h0
  have : (1/2 : ℝ) < (0 : ℝ) := by
    simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq, Complex.zero_re] using hz
  exact (lt_irrefl _) this

/-- `toDisk` is analytic on Ω. -/
lemma toDisk_analyticOn_Ω : AnalyticOn ℂ toDisk HalfPlaneOuterV2.Ω := by
  -- toDisk z = (z - 1) / z
  intro z hz
  have hz0 : z ≠ 0 := memΩ_ne_zero hz
  -- AnalyticAt for (· - 1)
  have h_sub : AnalyticAt ℂ (fun w : ℂ => w - (1 : ℂ)) z :=
    (AnalyticAt.id.sub analyticAt_const)
  -- AnalyticAt for inv
  have h_inv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) z :=
    AnalyticAt.inv (by simpa using hz0)
  -- AnalyticAt for division as multiplication by inv
  have h_div : AnalyticAt ℂ (fun w : ℂ => (w - 1) * w⁻¹) z := h_sub.mul h_inv
  -- Conclude
  simpa [toDisk, div_eq_mul_inv] using h_div


/-- Bridge (packaging form): Given the Cayley relation between `F` and a disk-side
transform `Hdisk`, together with half-plane analyticity, boundary integrability,
and the Poisson identity on Ω, produce the half-plane Poisson representation
record. This removes internal admits; callers supply the analytic facts. -/
def HalfPlanePoisson_from_Disk
  (F : ℂ → ℂ)
  (Hdisk : ℂ → ℂ)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuterV2.Ω)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    MeasureTheory.Integrable (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  (hReEq : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (F z).re = HalfPlaneOuterV2.poissonIntegral (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) z)
  : HalfPlaneOuterV2.HasPoissonRep F := by
  -- Package the provided half-plane facts directly; no internal admits.
  exact {
    analytic := hAnalytic
    integrable := hIntegrable
    formula := hReEq }

/-!
Change-of-variables (structural) adapter: from a disk Poisson representation to a
half‑plane Poisson representation of the real part, provided the Cayley boundary
change-of-variables holds at the level of the Poisson integrals.

This lemma captures the geometric bridge without re-proving kernel change-of-variables
internally. It is designed so that specialized callers can supply the equality of Poisson
integrals `hChange` and the map property `hMap`.
-/

open MeasureTheory

-- Add using declaration to make Integrable accessible without prefix
lemma HalfPlanePoisson_real_from_Disk
  (F Hdisk : ℂ → ℂ)
  (hDisk : DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuterV2.Ω)
  (hMap : ∀ z ∈ HalfPlaneOuterV2.Ω, toDisk z ∈ DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    MeasureTheory.Integrable (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  (hChange : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (∫ θ : ℝ, (Hdisk (DiskHardy.boundary θ)).re * DiskHardy.poissonKernel (toDisk z) θ)
      = (∫ t : ℝ, (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  : HalfPlaneOuterV2.HasPoissonRep F := by
  -- Derive the half‑plane real‑part identity from the disk representation and `hChange`.
  have hReEq : ∀ z ∈ HalfPlaneOuterV2.Ω,
      (F z).re = HalfPlaneOuterV2.poissonIntegral (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) z := by
    intro z hz
    -- From disk representation at w := toDisk z
    have hw : toDisk z ∈ DiskHardy.unitDisk := hMap z hz
    have hDiskEq : (Hdisk (toDisk z)).re
        = ∫ θ : ℝ, (Hdisk (DiskHardy.boundary θ)).re * DiskHardy.poissonKernel (toDisk z) θ :=
      hDisk.re_eq (toDisk z) hw
    -- Relate F z and Hdisk (toDisk z)
    have hRelz : F z = Hdisk (toDisk z) :=
      hRel hz
    -- Change variables on the integral side via the supplied identity `hChange`
    have hCoV := hChange z hz
    -- Conclude equality for Re F
    rw [HalfPlaneOuterV2.poissonIntegral, hRelz, hDiskEq]
    exact hCoV
  -- Package the half‑plane representation
  exact HalfPlanePoisson_from_Disk F Hdisk hRel hAnalytic hIntegrable hReEq

end CayleyAdapters
end AcademicFramework
end RH
