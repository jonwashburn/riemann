import rh.academic_framework.DiskHardy
-- (no additional mathlib imports needed here)
import rh.academic_framework.HalfPlaneOuterV2
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Exponential

@[simp] lemma two_sq_real : (2 : ℝ) ^ 2 = (4 : ℝ) := by norm_num

noncomputable section

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework
open scoped Real
@[simp] lemma boundary_as_add (t : ℝ) :
  HalfPlaneOuterV2.boundary t = ((1/2 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
  rfl

-- helper removed (not required)


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
    have : (1/2 : ℝ) < (0 : ℝ) := by
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

/-- Boundary angle parametrization transporting t ∈ ℝ ↦ θ ∈ (0, 2π):
    θ(t) = π − 2·arctan(2t). This realizes
    `DiskHardy.boundary (θ t) = boundaryToDisk t`. -/
def theta (t : ℝ) : ℝ := Real.pi - 2 * Real.arctan (2 * t)

lemma theta_measurable : Measurable theta :=
  (Continuous.measurable <|
    by
      have h1 : Continuous fun t : ℝ => (2 : ℝ) * t := continuous_const.mul continuous_id
      have h2 : Continuous fun t : ℝ => Real.arctan ((2 : ℝ) * t) := Real.continuous_arctan.comp h1
      have h3 : Continuous fun t : ℝ => 2 * Real.arctan (2 * t) := continuous_const.mul h2
      have h4 : Continuous fun t : ℝ => Real.pi - (2 * Real.arctan (2 * t)) :=
        continuous_const.sub h3
      exact h4)

lemma theta_hasDerivAt (t : ℝ) :
  HasDerivAt theta (-(4 : ℝ) / (1 + 4 * t^2)) t := by
  -- θ(t) = π − 2·arctan(2t)
  have h₁ : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 t := by
    simpa [id] using (hasDerivAt_id t).const_mul (2 : ℝ)
  -- Chain rule for arctan ∘ (t ↦ 2t)
  have h₂ := (Real.hasDerivAt_arctan (2 * t)).comp t h₁
  -- Multiply by the outer constant 2
  have h₃ := h₂.const_mul (2 : ℝ)
  -- Simplify the derivative value for 2·arctan(2t)
  have h₃' : HasDerivAt (fun t : ℝ => 2 * Real.arctan (2 * t)) (4 / (1 + 4 * t ^ 2)) t := by
    -- h₃ has derivative 2 * ((1 + (2t)^2)⁻¹ * 2); normalize it
    have hpow : (2 * t) ^ 2 = 4 * t ^ 2 := by
      ring
    have hval : 2 * (((1 + (2 * t) ^ 2)⁻¹) * 2) = 4 / (1 + 4 * t ^ 2) := by
      calc
        2 * (((1 + (2 * t) ^ 2)⁻¹) * 2)
            = 2 * (2 * (1 + (2 * t) ^ 2)⁻¹) := by simpa [mul_comm]
        _ = 4 * (1 + (2 * t) ^ 2)⁻¹ := by ring
        _ = 4 / (1 + (2 * t) ^ 2) := by simp [one_div, div_eq_mul_inv]
        _ = 4 / (1 + 4 * t ^ 2) := by simpa [hpow]
    simpa [hval] using h₃
  -- Use const_sub to build θ = π − (2·arctan(2t))
  have hθ : HasDerivAt (fun t : ℝ => Real.pi - (2 * Real.arctan (2 * t))) (-(4 / (1 + 4 * t ^ 2))) t :=
    (HasDerivAt.const_sub Real.pi h₃')
  -- normalize to the exact shape expected in the statement
  have hθ' : HasDerivAt theta (-(4 / (1 + 4 * t ^ 2))) t := by
    simpa [theta] using hθ
  simpa [neg_div] using hθ'

lemma theta_deriv_eq_neg_inv_absSq (t : ℝ) :
  deriv theta t = - (1 / (Complex.abs (HalfPlaneOuterV2.boundary t))^2) := by
  have h := (theta_hasDerivAt t).deriv
  -- simplify the derivative from arctan
  have hderiv : deriv theta t = - (4 / (1 + 4 * t^2)) := by
    simpa [neg_div] using h
  -- set s = boundary t to keep expressions compact
  set s : ℂ := HalfPlaneOuterV2.boundary t with hs
  -- |s|^2 = (1/4) + t^2
  have habs : (Complex.abs s)^2 = (1/4 : ℝ) + t^2 := by
    have hs' : s = ((1/2 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
      simpa [hs] using boundary_as_add t
    have hnorm' : Complex.normSq s = ((1/2 : ℝ) ^ 2 + t ^ 2) := by
      simpa [hs', Complex.normSq_apply, pow_two]
    have hhalf : ((1/2 : ℝ) ^ 2) = (1/4 : ℝ) := by norm_num
    calc
      (Complex.abs s)^2 = Complex.normSq s := by simpa [Complex.sq_abs]
      _ = (1/2 : ℝ) ^ 2 + t ^ 2 := hnorm'
      _ = (1/4 : ℝ) + t ^ 2 := by simpa [hhalf]
  -- rewrite -4/(1+4 t^2) as -(1 / |s|^2)
  have hden : (1 : ℝ) + 4 * t^2 = 4 * ((1/4 : ℝ) + t^2) := by ring
  calc
    deriv theta t = - (4 / (1 + 4 * t^2)) := hderiv
    _ = - (4 / (4 * ((1/4 : ℝ) + t^2))) := by simpa [hden]
    _ = - (1 / ((1/4 : ℝ) + t^2)) := by
          have : (4 : ℝ) ≠ 0 := by norm_num
          field_simp
    _ = - (1 / (Complex.abs s)^2) := by simpa [habs]
    _ = - (1 / (Complex.abs (HalfPlaneOuterV2.boundary t))^2) := by simpa [hs]

/-! ### Explicit Cayley ↔ unit-circle parametrization -/

/-! A closed form for `exp (i · 2 arctan y)` using trig closed forms in cartesian coordinates. -/
lemma exp_I_two_arctan_ratio (y : ℝ) :
  Complex.exp (Complex.I * (2 * Real.arctan y))
    = ((1 : ℝ) + Complex.I * y) / ((1 : ℝ) - Complex.I * y) := by
  -- Let a = arctan y; write y via s/c and factor c
  set a : ℝ := Real.arctan y with ha
  have hEuler :
      Complex.exp (Complex.I * (2 * a))
        = Complex.ofReal (Real.cos (2 * a))
          + Complex.I * Complex.ofReal (Real.sin (2 * a)) := by
    simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_cos, Complex.ofReal_sin]
      using (Complex.exp_mul_I (Complex.ofReal (2 * a)))
  set c : ℝ := Real.cos a with hc
  set s : ℝ := Real.sin a with hs
  have hc_val : c = 1 / Real.sqrt (1 + y^2) := by simpa [hc, ha] using Real.cos_arctan y
  have hs_val : s = y / Real.sqrt (1 + y^2) := by simpa [hs, ha] using Real.sin_arctan y
  have hc_ne : (c : ℝ) ≠ 0 := by
    have hpos : 0 < Real.sqrt (1 + y^2) := Real.sqrt_pos.mpr (by positivity)
    simpa [hc_val] using one_div_ne_zero (ne_of_gt hpos)
  -- Harmless disjunction that some algebraic normalizers may request; we close it explicitly
  have _hdisj : (Real.sqrt (1 + y ^ 2))⁻¹ = Real.cos a ∨ y = 0 := by
    left
    have hinv : (Real.sqrt (1 + y ^ 2))⁻¹ = 1 / Real.sqrt (1 + y ^ 2) := by simp
    have hone_over : (1 / Real.sqrt (1 + y ^ 2)) = Real.cos a := by
      simpa [hc] using hc_val.symm
    simpa [hinv, hone_over]
  have hs_rel : s = y * c := by
    calc
      s = y / Real.sqrt (1 + y^2) := by simpa [hs, ha] using Real.sin_arctan y
      _ = y * (1 / Real.sqrt (1 + y^2)) := by ring
      _ = y * c := by simpa [hc, hc_val]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc_ne
  -- Factor out c in the Möbius ratio and cancel it
  have hscC : (s : ℂ) = (y : ℂ) * (c : ℂ) := by
    have : (s : ℝ) = y * c := hs_rel
    simpa [Complex.ofReal_mul] using congrArg Complex.ofReal this
  have hnumfac : ((c : ℂ) + Complex.I * s) = (c : ℂ) * (1 + Complex.I * (y : ℂ)) := by
    calc
      (c : ℂ) + Complex.I * s
          = (c : ℂ) + Complex.I * ((y : ℂ) * (c : ℂ)) := by simpa [hscC]
      _ = (c : ℂ) * (1 + Complex.I * (y : ℂ)) := by ring
  have hdenfac : ((c : ℂ) - Complex.I * s) = (c : ℂ) * (1 - Complex.I * (y : ℂ)) := by
    calc
      (c : ℂ) - Complex.I * s
          = (c : ℂ) - Complex.I * ((y : ℂ) * (c : ℂ)) := by simpa [hscC]
      _ = (c : ℂ) * (1 - Complex.I * (y : ℂ)) := by ring
  -- Sum factorization on the base denominator
  have hsum_factor :
      (1 - Complex.I * (y : ℂ))⁻¹ + Complex.I * (y : ℂ) * (1 - Complex.I * (y : ℂ))⁻¹
        = ((1 : ℂ) + Complex.I * (y : ℂ)) * (1 - Complex.I * (y : ℂ))⁻¹ := by
    -- Let A = inv denom, B = I*y, and factor A + B*A = (1 + B)*A
    set A : ℂ := (1 - Complex.I * (y : ℂ))⁻¹
    set B : ℂ := Complex.I * (y : ℂ)
    have : A + B * A = (1 + B) * A := by
      simpa [add_mul, one_mul, add_comm, add_left_comm, add_assoc]
    simpa [A, B]
  have hsum_factor' :
      Complex.I * (y : ℂ) * (1 - Complex.I * (y : ℂ))⁻¹ + (1 - Complex.I * (y : ℂ))⁻¹
        = (Complex.I * (y : ℂ) + 1) * (1 - Complex.I * (y : ℂ))⁻¹ := by
    -- Use commutativity of addition to flip terms then apply the previous factorization
    have := hsum_factor
    simpa [add_comm, add_left_comm, add_assoc] using this
  -- Normalize the common-denominator sums into single fractions and cancel the factor `c`
  have hden' :
      (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))
        = (c : ℂ) * (1 - Complex.I * (y : ℂ)) := by ring
  have hnum' :
      (Complex.I * (y : ℂ) * (c : ℂ) + (c : ℂ))
        = (c : ℂ) * (Complex.I * (y : ℂ) + 1) := by ring
  -- Sum→product distribution at a factored denominator: c·D + (I y)·(c·D) = (c + (I y)c)·D
  have hsum_to_prod :
      (c : ℂ) * ( (c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))) )⁻¹
        + Complex.I * ((y : ℂ) * ((c : ℂ) * ( (c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))) )⁻¹))
        =
      ((c : ℂ) + Complex.I * ((y : ℂ) * (c : ℂ)))
        * ( (c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))) )⁻¹ := by
    set D : ℂ := ((c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))))⁻¹
    have : (c : ℂ) * D + (Complex.I * (y : ℂ)) * ((c : ℂ) * D)
            = ((c : ℂ) + (Complex.I * (y : ℂ)) * (c : ℂ)) * D := by
      ring_nf
    simpa [D, mul_comm, mul_left_comm, mul_assoc]
  -- In-place closure of the distribution goal
  have hsum_close :
      (c : ℂ) * ( (c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))) )⁻¹
        + Complex.I * ((y : ℂ) * ((c : ℂ) * ( (c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))) )⁻¹))
        =
      ((c : ℂ) + Complex.I * ((y : ℂ) * (c : ℂ)))
        * ( (c : ℂ) + -(Complex.I * ((y : ℂ) * (c : ℂ))) )⁻¹ := by
    simpa [sub_eq_add_neg] using hsum_to_prod
  -- Ratio alignment in mul_inv form via div_eq_mul_inv and cancellation of c
  have hratio_align :
      (Complex.I * (y : ℂ) + 1) * (1 - Complex.I * (y : ℂ))⁻¹
        =
      (Complex.I * (y : ℂ) * (c : ℂ) + (c : ℂ))
        * (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))⁻¹ := by
    have : ((Complex.I * (y : ℂ) + 1) / (1 - Complex.I * (y : ℂ)))
            =
           ((Complex.I * (y : ℂ) * (c : ℂ) + (c : ℂ))
              / (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))) := by
      simp [div_eq_mul_inv, hnum', hden', mul_comm, mul_left_comm, mul_assoc]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- Use the ratio alignment directly where needed
  have hratio_use :
      (Complex.I * (y : ℂ) + 1) * (1 - Complex.I * (y : ℂ))⁻¹
        =
      (Complex.I * (y : ℂ) * (c : ℂ) + (c : ℂ))
        * (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))⁻¹ := by
    simpa using hratio_align
  -- Sum equals product over factored denominator (ratio form and cancellation of `c`)
  have hcancel_c :
      Complex.I * (y : ℂ) * (1 - Complex.I * (y : ℂ))⁻¹ + (1 - Complex.I * (y : ℂ))⁻¹
        =
      Complex.I * (y : ℂ) * (c : ℂ) * (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))⁻¹
        + (c : ℂ) * (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))⁻¹ := by
    -- Left side to ratio
    have hLratio :
        Complex.I * (y : ℂ) * (1 - Complex.I * (y : ℂ))⁻¹ + (1 - Complex.I * (y : ℂ))⁻¹
          = ((Complex.I * (y : ℂ) + 1) / (1 - Complex.I * (y : ℂ))) := by
      simpa [div_eq_mul_inv] using hsum_factor'
    -- Right side to ratio
    have hRratio :
        Complex.I * (y : ℂ) * (c : ℂ) * (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))⁻¹
            + (c : ℂ) * (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ))⁻¹
          = (Complex.I * (y : ℂ) * (c : ℂ) + (c : ℂ))
              / (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ)) := by
      simp [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc]
    -- Cancel `c` from numerator and denominator
    have hreduce :
        ((Complex.I * (y : ℂ) + 1) / (1 - Complex.I * (y : ℂ)))
          =
        (Complex.I * (y : ℂ) * (c : ℂ) + (c : ℂ))
          / (-(Complex.I * (y : ℂ) * (c : ℂ)) + (c : ℂ)) := by
      simp [div_eq_mul_inv, hnum', hden', mul_comm, mul_left_comm, mul_assoc]
    exact hLratio.trans (hreduce.trans hRratio.symm)
  -- Direct Möbius normalization using cancellation of the nonzero factor `c`
  have hMobius :
      ((1 : ℂ) + Complex.I * y) / ((1 : ℂ) - Complex.I * y)
        = ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s) := by
    have hc0 : (c : ℂ) ≠ 0 := hcC
    calc
      ((1 : ℂ) + Complex.I * y) / ((1 : ℂ) - Complex.I * y)
          = ((c : ℂ) * (1 + Complex.I * (y : ℂ))) / ((c : ℂ) * (1 - Complex.I * (y : ℂ))) := by ring
      _ = ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s) := by
            simpa [hnumfac, hdenfac, div_eq_mul_inv, hc0, mul_comm, mul_left_comm, mul_assoc]
  -- Expand to cos/sin(2a)
  have hden_sq : ((c : ℂ) - Complex.I * s) * ((c : ℂ) + Complex.I * s)
      = Complex.ofReal (c ^ 2 + s ^ 2) := by
    ring_nf; simp [Complex.I_sq, Complex.ofReal_add, Complex.ofReal_mul, pow_two]
  have hnum_sq : ((c : ℂ) + Complex.I * s) * ((c : ℂ) + Complex.I * s)
      = Complex.ofReal (c ^ 2 - s ^ 2) + Complex.I * Complex.ofReal (2 * c * s) := by
    ring_nf; simp [Complex.ofReal_add, Complex.ofReal_mul, pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc]
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simpa [hc, hs, pow_two] using Real.cos_sq_add_sin_sq a
  have hR :
      ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s)
        = Complex.ofReal (Real.cos (2 * a))
          + Complex.I * Complex.ofReal (Real.sin (2 * a)) := by
    -- Convert to squared form and use double-angle identities
    have hfrac :
        ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s)
          =
        (Complex.ofReal (c ^ 2 - s ^ 2) + Complex.I * Complex.ofReal (2 * c * s))
          / Complex.ofReal (c ^ 2 + s ^ 2) := by
      have : ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s)
          = (((c : ℂ) + Complex.I * s) * ((c : ℂ) + Complex.I * s))
              / (((c : ℂ) - Complex.I * s) * ((c : ℂ) + Complex.I * s)) := by
        field_simp
      have : _ = (Complex.ofReal (c ^ 2 - s ^ 2) + Complex.I * Complex.ofReal (2 * c * s))
                    / Complex.ofReal (c ^ 2 + s ^ 2) := by
        simpa [hnum_sq, hden_sq]
      exact this
    have hstep :
        ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s)
          =
        Complex.ofReal (c ^ 2 - s ^ 2) + Complex.I * Complex.ofReal (2 * c * s) := by
      simpa [hcs] using hfrac
    -- identify with cos/sin(2a)
    have hcos2 : c ^ 2 - s ^ 2 = Real.cos (2 * a) := by
      simpa [hc, hs, pow_two] using (Real.cos_two_mul a)
    have hsin2 : 2 * c * s = Real.sin (2 * a) := by
      have := Real.sin_two_mul a
      simpa [hs, hc, two_mul, mul_comm, mul_left_comm, mul_assoc] using this
    -- Close the cartesian step
    simpa [hcos2, hsin2] using hstep
  -- Assemble with Euler form
  calc
    Complex.exp (Complex.I * (2 * Real.arctan y))
        = Complex.exp (Complex.I * (2 * a)) := by simpa [ha]
    _ = Complex.ofReal (Real.cos (2 * a)) + Complex.I * Complex.ofReal (Real.sin (2 * a)) := hEuler
    _ = ((c : ℂ) + Complex.I * s) / ((c : ℂ) - Complex.I * s) := hR.symm
    _ = ((1 : ℂ) + Complex.I * y) / ((1 : ℂ) - Complex.I * y) := hMobius.symm

/-- Conjugated identity: `exp(-i·(2·arctan y)) = (1 - i y)/(1 + i y)`. -/
lemma exp_negI_two_arctan_ratio (y : ℝ) :
  Complex.exp (- Complex.I * (2 * Real.arctan y))
    = ((1 : ℝ) - Complex.I * y) / ((1 : ℝ) + Complex.I * y) := by
  have hpos := exp_I_two_arctan_ratio y
  -- Take inverses on both sides of the positive-angle identity
  have hinv := congrArg Inv.inv hpos
  -- Normalize inverses of ratios
  have hinv' : (Complex.exp (Complex.I * (2 * Real.arctan y)))⁻¹
      = ((1 : ℝ) - Complex.I * y) / ((1 : ℝ) + Complex.I * y) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hinv
  calc
    Complex.exp (- Complex.I * (2 * Real.arctan y))
        = Complex.exp (-(Complex.I * (2 * Real.arctan y))) := by ring
    _ = (Complex.exp (Complex.I * (2 * Real.arctan y)))⁻¹ := by
          simpa using Complex.exp_neg (Complex.I * (2 * Real.arctan y))
    _ = ((1 : ℝ) - Complex.I * y) / ((1 : ℝ) + Complex.I * y) := by
          simpa using hinv'

/-- Parametrization identity along the boundary circle. -/
lemma boundaryToDisk_param (t : ℝ) :
  DiskHardy.boundary (theta t) = boundaryToDisk t := by
  -- boundaryToDisk t = (s-1)/s for s = 1/2 + i t
  have hs : HalfPlaneOuterV2.boundary t = { re := (1/2 : ℝ), im := t } := by
    simpa using HalfPlaneOuterV2.boundary_mk_eq t
  have hrat : boundaryToDisk t
      = ((-1 : ℝ) + (2 : ℝ) * Complex.I * t) / ((1 : ℝ) + (2 : ℝ) * Complex.I * t) := by
    simp [boundaryToDisk, toDisk, hs, div_eq_mul_inv]
    field_simp
  -- LHS = exp(i·θ(t)) with θ(t) = π − 2 arctan(2 t)
  have hpi : Complex.exp (Complex.I * Real.pi) = (-1 : ℂ) := by simpa using Complex.exp_pi_mul_I
  -- Split exp(i(π - α)) = exp(iπ) * exp(-i α) and rewrite with hpi
  have hsplit :
      Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (2 * t)))
        = - Complex.exp (- Complex.I * (2 * Real.arctan (2 * t))) := by
    have : Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (2 * t)))
            = Complex.exp (Complex.I * Real.pi) * Complex.exp (- Complex.I * (2 * Real.arctan (2 * t))) := by
      simpa [Complex.exp_add, sub_eq_add_neg]
    simpa [hpi, mul_comm] using this
  -- Use the explicit ratio identity and normalize
  have hRatio := exp_negI_two_arctan_ratio (2 * t)
  have hLHS :
      Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (2 * t)))
        = ((-1 : ℝ) + (2 : ℝ) * Complex.I * t) / ((1 : ℝ) + (2 : ℝ) * Complex.I * t) := by
    have hx : Complex.exp (- Complex.I * (2 * Real.arctan (2 * t)))
        = ((1 : ℝ) - Complex.I * (2 * t)) / ((1 : ℝ) + Complex.I * (2 * t)) := by
      simpa using hRatio
    calc
      Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (2 * t)))
          = - Complex.exp (- Complex.I * (2 * Real.arctan (2 * t))) := hsplit
      _ = - (((1 : ℝ) - Complex.I * (2 * t)) / ((1 : ℝ) + Complex.I * (2 * t))) := by
            simpa [hx]
      _ = ((-((1 : ℂ) - Complex.I * (2 * t))) / ((1 : ℂ) + Complex.I * (2 * t))) := by
            simp [neg_div, div_eq_mul_inv]
      _ = ((-1 : ℂ) + (2 : ℝ) * Complex.I * t) / ((1 : ℂ) + (2 : ℂ) * Complex.I * t) := by
            ring_nf
      _ = ((-1 : ℝ) + (2 : ℝ) * Complex.I * t) / ((1 : ℝ) + (2 : ℝ) * Complex.I * t) := by
            ring_nf
  -- Conclude by comparing the two explicit ratios
  calc
    DiskHardy.boundary (theta t)
        = Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (2 * t))) := by
            simpa [DiskHardy.boundary, theta]
    _ = ((-1 : ℝ) + (2 : ℝ) * Complex.I * t) / ((1 : ℝ) + (2 : ℝ) * Complex.I * t) := hLHS
    _ = boundaryToDisk t := hrat.symm

/-- Points of Ω are nonzero: if `Re z > 1/2` then `z ≠ 0`. -/
lemma memΩ_ne_zero {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) : z ≠ 0 := by
  intro h0
  have hzRe : (1/2 : ℝ) < z.re := by
    simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hz
  have hlt : (1/2 : ℝ) < 0 := by
    simpa [h0, Complex.zero_re] using hzRe
  have hnot : ¬ ((1/2 : ℝ) < 0) := by norm_num
  exact hnot hlt

/-- `toDisk` is analytic on Ω. -/
lemma toDisk_analyticOn_Ω : AnalyticOn ℂ toDisk HalfPlaneOuterV2.Ω := by
  -- toDisk z = (z - 1) / z is analytic on Ω (denominator nonzero on Ω)
  have h_id : AnalyticOn ℂ (fun z : ℂ => z) HalfPlaneOuterV2.Ω := analyticOn_id
  have h_const : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) HalfPlaneOuterV2.Ω := analyticOn_const
  have h_sub : AnalyticOn ℂ (fun z : ℂ => z - (1 : ℂ)) HalfPlaneOuterV2.Ω := h_id.sub h_const
  have h_div : AnalyticOn ℂ (fun z : ℂ => (z - 1) / z) HalfPlaneOuterV2.Ω :=
    h_sub.div h_id (by intro z hz; exact memΩ_ne_zero hz)
  simpa [toDisk] using h_div


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
