/-
Copyright (c) 2024 Riemann Hypothesis Contributors. All rights reserved.
Released under Apache 2.0 license as described in the project LICENSE file.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Convex.Basic

/-!
# Whitney Geometry Definitions for Half-Plane

This file provides the core geometric definitions for Whitney boxes and tents
in the upper half-plane, used throughout the RS proof machinery.

## Main definitions

* `RS.Whitney.tent` - The Carleson box T(I) = I × (0, α|I|] over interval I
* `RS.Whitney.shadow` - The boundary projection/base interval of a Whitney box
* `RS.Whitney.fixed_geometry` - Predicate for boxes with controlled aspect ratio
* `RS.boxEnergy` - The weighted energy ∬_Q |∇U|² σ dt dσ

## Implementation notes

We use the standard upper half-plane {z : ℂ | z.im > 0} with boundary ℝ.
Whitney boxes have comparable height and width (fixed eccentricity).
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators MeasureTheory

namespace RH
namespace RS
namespace Whitney

-- Standard aperture parameter for Carleson boxes
def standardAperture : ℝ := 2

/-- The length of an interval (Lebesgue measure) -/
def length (I : Set ℝ) : ℝ := (volume I).toReal

/-- The Carleson tent/box over interval I with aperture α -/
def tent (I : Set ℝ) (α : ℝ := standardAperture) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ I ∧ 0 < p.2 ∧ p.2 ≤ α * length I}

/-- The shadow (base interval) of a Whitney box Q -/
def shadow (Q : Set (ℝ × ℝ)) : Set ℝ := {t : ℝ | ∃ σ > 0, (t, σ) ∈ Q}

/-- The shadow length of a Whitney box -/
def shadowLen (Q : Set (ℝ × ℝ)) : ℝ := length (shadow Q)

/-- A box Q has fixed Whitney geometry if it has controlled aspect ratio.
    Specifically: height ≈ width, bounded eccentricity, and Q ⊆ tent(shadow Q) -/
structure fixed_geometry (Q : Set (ℝ × ℝ)) : Prop where
  -- There exist center and dimensions with controlled ratios
  center : ℝ × ℝ
  width : ℝ
  height : ℝ
  center_in : center ∈ Q
  width_pos : 0 < width
  height_pos : 0 < height
  -- Fixed aspect ratio: height comparable to width
  aspect_lower : height ≥ width / 4
  aspect_upper : height ≤ 4 * width
  -- Q is essentially a rectangle around center
  subset_rect : Q ⊆ {p : ℝ × ℝ | |p.1 - center.1| ≤ width / 2 ∧
                                   |p.2 - center.2| ≤ height / 2}
  rect_subset : {p : ℝ × ℝ | |p.1 - center.1| < width / 2 ∧
                              0 < p.2 ∧ p.2 < center.2 + height / 2} ⊆ Q
  -- Q lies in the upper half-plane
  upper : Q ⊆ {p : ℝ × ℝ | 0 < p.2}
  -- Center is not too far above the bottom
  center_le_top : center.2 ≤ height / 2
  -- Height is bounded by shadow length
  height_shadow : height ≤ 2 * shadowLen Q

/-- A Whitney box Q is in the tent over I if its shadow is contained in I -/
def in_tent_over (I : Set ℝ) (Q : Set (ℝ × ℝ)) : Prop :=
  shadow Q ⊆ I

/-- The box energy measure μ(Q) = ∬_Q |∇U|² σ dt dσ -/
def boxEnergy (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) : ℝ :=
  (∫ p in Q, ‖gradU p‖² * p.2 ∂σ).toReal

/-- The tent energy over interval I -/
def tentEnergy (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (I : Set ℝ) : ℝ :=
  boxEnergy gradU σ (tent I)

/-- Fixed overlap constant for Whitney shadow packing -/
def shadowOverlapConst : ℝ := 10

/-! ### Basic properties -/

/-- Monotonicity of interval length under set inclusion. -/
lemma length_mono {I J : Set ℝ} (h : I ⊆ J) : length I ≤ length J := by
  unfold length
  exact ENNReal.toReal_mono (ne_top_of_lt volume_finite) (volume.mono h)

/-- Monotonicity of tents with respect to base-interval inclusion. -/
lemma tent_mono {I J : Set ℝ} (h : I ⊆ J) (α : ℝ) : tent I α ⊆ tent J α := by
  intro p hp
  simp only [tent, Set.mem_setOf] at hp ⊢
  obtain ⟨hI, hp1, hp2⟩ := hp
  refine ⟨h hI, hp1, ?_⟩
  apply le_trans hp2
  apply mul_le_mul_of_nonneg_left _ (le_trans (le_of_lt hp1) hp2)
  exact length_mono h

/-- Monotonicity of box energy under set inclusion (assuming finiteness on the larger set). -/
lemma boxEnergy_mono {gradU : (ℝ × ℝ) → ℝ × ℝ} {σ : Measure (ℝ × ℝ)}
    {P Q : Set (ℝ × ℝ)} (h : P ⊆ Q)
    (hPmeas : MeasurableSet P) (hQmeas : MeasurableSet Q)
    (hfinQ : (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ) < ∞) :
    boxEnergy gradU σ P ≤ boxEnergy gradU σ Q := by
  -- Work at the level of lintegrals with nonnegative integrand and then apply toReal_mono
  unfold boxEnergy
  set IP : ℝ≥0∞ := ∫⁻ p in P, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ
  set IQ : ℝ≥0∞ := ∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ
  change IP.toReal ≤ IQ.toReal
  -- Monotonicity after ensuring finiteness of the larger integral
  apply ENNReal.toReal_mono
  · -- finiteness provided by hypothesis
    simpa [IQ] using hfinQ
  · -- Lintegral monotonicity on measurable sets
    have hmono :
        (∫⁻ p in P, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ)
          ≤ (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖² * p.2) ∂σ) := by
      exact Measure.lintegral_mono_set (μ := σ) hPmeas hQmeas h
    simpa [IP, IQ] using hmono

/-- The tent set `tent I α` is measurable. -/
lemma measurableSet_tent {I : Set ℝ} {α : ℝ} (hI : MeasurableSet I) :
  MeasurableSet (tent I α) := by
  -- tent I α = {p | p.1 ∈ I} ∩ {p | 0 < p.2} ∩ {p | p.2 ≤ α * length I}
  -- All three pieces are measurable under the product σ-algebra
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 ∈ I} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using hI.preimage measurable_fst
  have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using (MeasurableSet_Ioi.preimage measurable_snd)
  have h3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ α * length I} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using (MeasurableSet_Iic.preimage measurable_snd)
  have : tent I α =
      ({p : ℝ × ℝ | p.1 ∈ I} ∩ {p : ℝ × ℝ | 0 < p.2}) ∩ {p : ℝ × ℝ | p.2 ≤ α * length I} := by
    ext p; constructor
    · intro hp; rcases hp with ⟨hpI, hp0, hpU⟩; exact ⟨⟨by simpa using hpI, by simpa using hp0⟩, by simpa using hpU⟩
    · intro hp; rcases hp with ⟨⟨hpI, hp0⟩, hpU⟩; exact ⟨by simpa using hpI, by simpa using hp0, by simpa using hpU⟩
  simpa [this] using (h1.inter h2).inter h3

/-- On a tent, the weighted lintegral of `‖∇U‖²·σ` is finite if `‖∇U‖²` is L² on the tent. -/
lemma finite_lintegral_on_tent_of_L2
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (I : Set ℝ) (α : ℝ)
  (hI : MeasurableSet I)
  (hL2 : IntegrableOn (fun p => ‖gradU p‖^2) (tent I α) volume) :
  (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2) ) < ∞ := by
  -- On tents, 0 < p.2 ≤ α * length I, so p.2 is essentially bounded by a constant C.
  -- Hence ofReal (‖gradU‖^2 * p.2) ≤ ENNReal.ofReal C * ofReal (‖gradU‖^2),
  -- and finiteness follows from the L² bound of ‖gradU‖.
  have hTent : MeasurableSet (tent I α) := measurableSet_tent (hI := hI)
  set C : ℝ := max (α * length I) 0
  have hCnonneg : 0 ≤ C := le_max_right _ _
  -- a.e. bound σ ≤ C on the tent
  have hBound_base : ∀ᵐ p ∂volume, p ∈ tent I α → p.2 ≤ C := by
    refine Filter.eventually_of_forall ?_;
    intro p hp
    have hpU : p.2 ≤ α * length I := by simpa [tent, Set.mem_setOf_eq] using hp.2.2
    exact le_trans hpU (le_max_left _ _)
  have hBound_ae : ∀ᵐ p ∂(Measure.restrict volume (tent I α)), p.2 ≤ C := by
    simpa [ae_restrict_iff, hTent] using hBound_base
  -- Pointwise a.e. bound for the integrand on the tent
  have hpoint_ae :
      (∀ᵐ p ∂(Measure.restrict volume (tent I α)),
        ENNReal.ofReal (‖gradU p‖^2 * p.2)
          ≤ ENNReal.ofReal C * ENNReal.ofReal (‖gradU p‖^2)) := by
    refine hBound_ae.mono ?_;
    intro p hpC
    have hmul : ‖gradU p‖^2 * p.2 ≤ ‖gradU p‖^2 * C :=
      mul_le_mul_of_nonneg_left hpC (by exact sq_nonneg _)
    have : ENNReal.ofReal (‖gradU p‖^2 * p.2)
            ≤ ENNReal.ofReal (‖gradU p‖^2 * C) :=
      ENNReal.ofReal_le_ofReal_iff.mpr hmul
    -- rewrite RHS as constant * ofReal(‖gradU‖^2)
    simpa [ENNReal.ofReal_mul hCnonneg (sq_nonneg _), mul_comm, mul_left_comm, mul_assoc]
      using this
  -- Integrate both sides over the tent (restricted measure)
  have hlin :
      (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2))
        ≤ ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
    have hconst :
        (∫⁻ p in tent I α, (fun _ => ENNReal.ofReal C) * ENNReal.ofReal (‖gradU p‖^2))
          = ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
      simp [Measure.restrict_apply, hTent]
    refine le_trans (Measure.lintegral_mono_ae hpoint_ae) ?_;
    simpa [hconst]
  -- Use L²-integrability to conclude finiteness of the RHS
  have hfin_sq : (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) < ∞ := by
    -- Standard: IntegrableOn f ⇒ lintegral (ofReal |f|) < ∞
    have hInt := hL2.hasFiniteIntegral
    simpa [Measure.restrict_apply, hTent, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using hInt
  exact lt_of_le_of_lt hlin (mul_lt_top (by simpa using ENNReal.ofReal_lt_top) hfin_sq)

/-- Monotonicity of box energy on tents when the base intervals are nested. -/
lemma boxEnergy_mono_tent
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (I J : Set ℝ) (α : ℝ)
  (hIJ : I ⊆ J) (hI : MeasurableSet I) (hJ : MeasurableSet J)
  (hL2 : IntegrableOn (fun p => ‖gradU p‖^2) (tent J α) volume) :
  boxEnergy gradU volume (tent I α) ≤ boxEnergy gradU volume (tent J α) := by
  -- Reduce to the general monotonicity using tent_mono and discharge finiteness via finite_lintegral_on_tent_of_L2
  have hsubset : tent I α ⊆ tent J α := tent_mono hIJ α
  -- Use the general lemma; provide measurability and finiteness to close admits
  have hTentJ_meas : MeasurableSet (tent J α) := measurableSet_tent (hI := hJ)
  have hfin : (∫⁻ p in tent J α, ENNReal.ofReal (‖gradU p‖^2 * p.2)) < ∞ :=
    finite_lintegral_on_tent_of_L2 (gradU := gradU) (I := J) (α := α) (hI := hJ)
      (by
        -- L² on J implies L² on J for the same set (identity)
        simpa using hL2)
  -- Apply the strengthened monotonicity with measurability and finiteness
  exact boxEnergy_mono (gradU := gradU) (σ := volume) (P := tent I α) (Q := tent J α)
    hsubset (measurableSet_tent (hI := hI)) hTentJ_meas hfin

/-- Points in a fixed-geometry box have positive height `p.2 > 0`. -/
lemma fixed_geometry_upper {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    ∀ {p : ℝ × ℝ}, p ∈ Q → 0 < p.2 := by
  intro p hp
  have : p ∈ {p : ℝ × ℝ | 0 < p.2} := h.upper hp
  simpa [Set.mem_setOf] using this

/-- For fixed geometry, the vertical center is at height at most `height/2`. -/
lemma fixed_geometry_center_le_top {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    h.center.2 ≤ h.height / 2 := h.center_le_top

/-- A fixed-geometry box is contained in the tent over its own shadow. -/
lemma fixed_geometry_subset_tent (Q : Set (ℝ × ℝ)) (h : fixed_geometry Q) :
    Q ⊆ tent (shadow Q) := by
  intro p hp
  -- Unpack the fixed geometry structure
  obtain ⟨center, width, height, hcenter, hwidth, hheight,
          haspect_lo, haspect_hi, hQsub, hQsup, hheight_shadow⟩ := h
  simp only [tent, Set.mem_setOf]

  -- From hQsub, p is in the rectangle around center
  have hp_rect : |p.1 - center.1| ≤ width / 2 ∧ |p.2 - center.2| ≤ height / 2 :=
    hQsub hp

  -- p.1 is in the shadow by definition
  have hp1_shadow : p.1 ∈ shadow Q := by
    use p.2
    constructor
    · -- Need p.2 > 0
      exact fixed_geometry_upper h hp
    · exact hp

  refine ⟨hp1_shadow, ?_, ?_⟩
  · -- Show p.2 > 0
    exact fixed_geometry_upper h hp
  · -- Show p.2 ≤ standardAperture * length (shadow Q)
    calc p.2
        ≤ center.2 + height / 2 := by
          -- From |p.2 - center.2| ≤ height/2
          have : p.2 - center.2 ≤ height / 2 := by
            have := hp_rect.right
            -- |x| ≤ a ⇒ x ≤ a
            exact (abs_le.mp this).right
          linarith
    _ ≤ height := by
          -- Using center.2 ≤ height/2
          have := fixed_geometry_center_le_top h
          linarith
    _ ≤ 2 * shadowLen Q := hheight_shadow
    _ = standardAperture * shadowLen Q := by rfl

/-- Monotonicity of the shadow: if `Q ⊆ R` then `shadow Q ⊆ shadow R`. -/
lemma shadow_mono {Q R : Set (ℝ × ℝ)} (hQR : Q ⊆ R) : shadow Q ⊆ shadow R := by
  intro t ht
  rcases ht with ⟨σ, hσpos, hmem⟩
  exact ⟨σ, hσpos, hQR hmem⟩

/-- Positive shadow length under fixed Whitney geometry. -/
lemma fixed_geometry_shadowLen_pos {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    0 < shadowLen Q := by
  -- From `height ≤ 2·|shadow|` and `height>0`, deduce `|shadow|>0`.
  have hhalf_pos : 0 < h.height / 2 := by nlinarith [h.height_pos]
  have hdiv : h.height / 2 ≤ shadowLen Q := by
    -- divide `h.height ≤ 2 * shadowLen Q` by 2 > 0
    have : h.height ≤ shadowLen Q * 2 := by simpa [mul_comm] using h.height_shadow
    exact (div_le_iff (by norm_num : (0:ℝ) < 2)).mpr this
  exact lt_of_lt_of_le hhalf_pos hdiv

/-- The horizontal core interval of width `h.width` is contained in the shadow. -/
/-- The horizontal core interval is contained in the shadow for fixed geometry. -/
lemma fixed_geometry_shadow_core_subset {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    {t : ℝ | |t - h.center.1| < h.width / 2} ⊆ shadow Q := by
  intro t ht
  -- Choose a uniform height inside the rectangle witness
  let σ := min (h.center.2 / 2) (h.height / 4)
  have hσ_pos : 0 < σ := by
    have hc_pos : 0 < h.center.2 := by
      -- center ∈ Q and Q ⊆ {p | 0 < p.2}
      exact fixed_geometry_upper h h.center_in
    have hc2_pos : 0 < h.center.2 / 2 := by nlinarith
    have hh4_pos : 0 < h.height / 4 := by nlinarith [h.height_pos]
    have : 0 < min (h.center.2 / 2) (h.height / 4) := lt_min hc2_pos hh4_pos
    simpa [σ]
  have hσ_top : σ < h.center.2 + h.height / 2 := by
    -- Since σ ≤ h.center.2/2 and σ ≤ h.height/4, certainly σ < center.2 + height/2
    have hle1 : σ ≤ h.center.2 / 2 := by exact min_le_left _ _
    have hc2_lt : (h.center.2 / 2) < h.center.2 + h.height / 2 := by
      have : 0 < h.center.2 / 2 + h.height / 2 := by
        have hc_pos : 0 < h.center.2 := by exact fixed_geometry_upper h h.center_in
        have hh_pos : 0 < h.height := h.height_pos
        nlinarith
      nlinarith
    exact lt_of_le_of_lt hle1 hc2_lt
  -- Use the rectangle inclusion
  have hrect : |t - h.center.1| < h.width / 2 ∧ 0 < σ ∧ σ < h.center.2 + h.height / 2 := by
    exact ⟨ht, hσ_pos, hσ_top⟩
  -- Points in the rectangle are in Q
  have hmem : (t, σ) ∈ Q := by
    exact h.rect_subset ⟨by
      -- expand rectangle predicates
      simpa using hrect.1, hrect.2.1, hrect.2.2⟩
  -- Hence t lies in the shadow
  exact ⟨σ, hσ_pos, hmem⟩

/-- Length of a symmetric open interval described by `|t - c| < r`. -/
/-- Length of the symmetric open interval `{t | |t−c| < r}` equals `2r`. -/
lemma length_abs_lt (c r : ℝ) (hr : 0 < r) :
    length ({t : ℝ | |t - c| < r}) = 2 * r := by
  have : {t : ℝ | |t - c| < r} = Set.Ioo (c - r) (c + r) := by
    ext t; constructor <;> intro ht
    · have : -r < t - c ∧ t - c < r := by simpa [abs_lt] using ht
      constructor <;> linarith
    · rcases ht with ⟨hlt, hrt⟩
      have : |t - c| < r := by
        have : -r < t - c ∧ t - c < r := ⟨hlt, hrt⟩
        simpa [abs_lt] using this
      simpa using this
  simp [length, this, Real.volume_Ioo, sub_eq, add_comm, add_left_comm, add_assoc]

/-- The shadow length dominates the core width. -/
/-- Under fixed geometry, the width is bounded by the shadow length. -/
lemma fixed_geometry_width_le_shadowLen {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    h.width ≤ shadowLen Q := by
  -- Use monotonicity of measure via the core-subset lemma
  have hsub : {t : ℝ | |t - h.center.1| < h.width / 2} ⊆ shadow Q :=
    fixed_geometry_shadow_core_subset h
  have hmono := length_mono (I := {t : ℝ | |t - h.center.1| < h.width / 2}) (J := shadow Q) hsub
  -- Compute the core length as the width
  have hcore : length ({t : ℝ | |t - h.center.1| < h.width / 2}) = h.width := by
    have hwpos : 0 < h.width := h.width_pos
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc]
      using length_abs_lt h.center.1 (h.width / 2) (by nlinarith)
  simpa [shadowLen, hcore] using hmono

/-- Shadow length and width are comparable under fixed Whitney geometry. -/
/-- Coarse comparability: `width ≤ 8 · shadowLen` under fixed geometry. -/
lemma fixed_geometry_width_le_eight_shadowLen {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    h.width ≤ 8 * shadowLen Q := by
  -- From `height ≥ width/4` and `height ≤ 2·|shadow|` obtain `width ≤ 8·|shadow|`.
  have hW4 : h.width / 4 ≤ h.height := by
    -- rearrange `aspect_lower : height ≥ width/4`
    simpa [le_comm] using h.aspect_lower
  have hH : h.height ≤ 2 * shadowLen Q := h.height_shadow
  have : h.width / 4 ≤ 2 * shadowLen Q := le_trans hW4 hH
  have hpos4 : (0 : ℝ) < 4 := by norm_num
  -- multiply both sides by 4
  have : h.width ≤ 8 * shadowLen Q := by
    have := (mul_le_mul_of_nonneg_right (a := h.width / 4) (b := 2 * shadowLen Q) (c := 4)
      (by linarith : 0 ≤ (4 : ℝ)) this)
    -- (h.width/4)*4 ≤ (2*shadowLen)*4 = 8*shadowLen
    simpa [mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div, two_mul] using this
  exact this

/-! ## Overlap/packing interface (pass-through)

These helpers expose the intended Whitney shadow packing inequality in a
lightweight, pass-through form so downstream modules can depend on the name
without pulling in a full packing proof here. -/

/-- Pass-through packing helper: expose the shadow overlap bound name. -/
theorem shadow_overlap_bound_pass
  {ι : Type*} (S : Finset ι)
  (Q : ι → Set (ℝ × ℝ)) (I : Set ℝ)
  (h : (∑ i in S, shadowLen (Q i)) ≤ shadowOverlapConst * length I) :
  (∑ i in S, shadowLen (Q i)) ≤ shadowOverlapConst * length I := h

end Whitney

-- Make boxEnergy available at RS level
def boxEnergy := Whitney.boxEnergy
def tentEnergy := Whitney.tentEnergy
def length := Whitney.length

end RS
end RH
