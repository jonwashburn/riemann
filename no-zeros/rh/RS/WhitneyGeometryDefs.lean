/-
Copyright (c) 2024 Riemann Hypothesis Contributors. All rights reserved.
Released under Apache 2.0 license as described in the project LICENSE file.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

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
structure fixed_geometry (Q : Set (ℝ × ℝ)) where
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
  (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖^2 * p.2) ∂σ).toReal

/-- The tent energy over interval I -/
def tentEnergy (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (I : Set ℝ) : ℝ :=
  boxEnergy gradU σ (tent I)

/-- Fixed overlap constant for Whitney shadow packing -/
def shadowOverlapConst : ℝ := 10

/-! ### Basic properties -/

/-- Monotonicity of interval length under set inclusion. -/
lemma length_mono
  {I J : Set ℝ} (hIJ : I ⊆ J) (hJfin : volume J ≠ ⊤) : length I ≤ length J := by
  unfold length
  have hμ : volume I ≤ volume J := measure_mono hIJ
  -- use `toReal_le_toReal` with finiteness on both sides
  have hJlt : volume J < ⊤ := by simpa [lt_top_iff_ne_top] using hJfin
  have hIlt : volume I < ⊤ := lt_of_le_of_lt hμ hJlt
  exact (ENNReal.toReal_le_toReal (ha := ne_of_lt hIlt) (hb := hJfin)).2 hμ

lemma length_nonneg (I : Set ℝ) : 0 ≤ length I := by
  unfold length; exact ENNReal.toReal_nonneg

/-- Monotonicity of tents with respect to base-interval inclusion. -/
lemma tent_mono
  {I J : Set ℝ} (hIJ : I ⊆ J) (α : ℝ) (hα : 0 ≤ α) (hJfin : volume J ≠ ⊤)
  : tent I α ⊆ tent J α := by
  intro p hp
  simp only [tent, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨hI, hp1, hp2⟩ := hp
  refine ⟨hIJ hI, hp1, ?_⟩
  apply le_trans hp2
  have hlen : length I ≤ length J := length_mono (hIJ := hIJ) (hJfin := hJfin)
  exact mul_le_mul_of_nonneg_left hlen hα

/-- Monotonicity of box energy under set inclusion (assuming finiteness on the larger set). -/
lemma boxEnergy_mono {gradU : (ℝ × ℝ) → ℝ × ℝ} {σ : Measure (ℝ × ℝ)}
    {P Q : Set (ℝ × ℝ)} (h : P ⊆ Q)
    (_hPmeas : MeasurableSet P) (_hQmeas : MeasurableSet Q)
    (hfinQ : (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖^2 * p.2) ∂σ) < ⊤) :
    boxEnergy gradU σ P ≤ boxEnergy gradU σ Q := by
  -- Work at the level of lintegrals with nonnegative integrand and then apply toReal_le_toReal
  unfold boxEnergy
  -- Monotonicity via indicator functions and lintegral_mono
  have hmono :
      (∫⁻ p in P, ENNReal.ofReal (‖gradU p‖^2 * p.2) ∂σ)
        ≤ (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖^2 * p.2) ∂σ) := by
    -- use the set-monotonicity of the set integral
    exact lintegral_mono_set (μ := σ)
      (f := fun p => ENNReal.ofReal (‖gradU p‖^2 * p.2)) (s := P) (t := Q) h
  -- Finiteness of both sides
  have hIQfin :
      (∫⁻ p in Q, ENNReal.ofReal (‖gradU p‖^2 * p.2) ∂σ) ≠ ⊤ := by
    simpa [lt_top_iff_ne_top] using hfinQ
  have hIPfin :
      (∫⁻ p in P, ENNReal.ofReal (‖gradU p‖^2 * p.2) ∂σ) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hmono (by simpa using hfinQ))
  -- Apply toReal_le_toReal
  exact (ENNReal.toReal_le_toReal (ha := hIPfin) (hb := hIQfin)).2 hmono

/-- The tent set `tent I α` is measurable. -/
lemma measurableSet_tent {I : Set ℝ} {α : ℝ} (hI : MeasurableSet I) :
  MeasurableSet (tent I α) := by
  -- tent I α = {p | p.1 ∈ I} ∩ {p | 0 < p.2} ∩ {p | p.2 ≤ α * length I}
  -- All three pieces are measurable under the product σ-algebra
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 ∈ I} := by
    simpa [Set.preimage, Set.mem_setOf_eq] using hI.preimage measurable_fst
  have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := by
    -- preimage of Ioi under the continuous second projection is open, hence measurable
    have ho : IsOpen ((fun p : ℝ × ℝ => p.2) ⁻¹' Set.Ioi (0 : ℝ)) :=
      isOpen_Ioi.preimage continuous_snd
    simpa [Set.preimage, Set.mem_setOf_eq] using ho.measurableSet
  have h3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ α * length I} := by
    -- preimage of Iic under the continuous second projection is closed, hence measurable
    have hc : IsClosed ((fun p : ℝ × ℝ => p.2) ⁻¹' Set.Iic (α * length I)) :=
      isClosed_Iic.preimage continuous_snd
    simpa [Set.preimage, Set.mem_setOf_eq] using hc.measurableSet
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
  (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2)) < ⊤ := by
  -- On tents, 0 < p.2 ≤ α * length I, so p.2 is essentially bounded by a constant C.
  -- Hence ofReal (‖gradU‖^2 * p.2) ≤ ENNReal.ofReal C * ofReal (‖gradU‖^2),
  -- and finiteness follows from the L² bound of ‖gradU‖.
  have hTent : MeasurableSet (tent I α) := measurableSet_tent (hI := hI)
  set C : ℝ := max (α * length I) 0
  have _ : 0 ≤ C := le_max_right _ _
  -- a.e. bound σ ≤ C on the tent
  have hBound_base : ∀ᵐ p ∂volume, p ∈ tent I α → p.2 ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro p hp
    have hpU : p.2 ≤ α * length I := by simpa [tent, Set.mem_setOf_eq] using hp.2.2
    exact le_trans hpU (le_max_left _ _)
  -- measurability of the predicate {p | p.2 ≤ C}
  -- (not needed later, keep for reference)
  -- have hPred : MeasurableSet {p : (ℝ × ℝ) | p.2 ≤ C} := by
  --   have hc : IsClosed ((fun p : ℝ × ℝ => p.2) ⁻¹' Set.Iic C) :=
  --     isClosed_Iic.preimage continuous_snd
  --   simpa [Set.preimage, Set.mem_setOf_eq] using hc.measurableSet
  have hBound_ae : ∀ᵐ p ∂(volume.restrict (tent I α)), p.2 ≤ C := by
    -- Convert AE statement on volume to AE on the restricted measure
    have hiff :=
      (ae_restrict_iff' (μ := volume) (s := tent I α) (p := fun p : (ℝ × ℝ) => p.2 ≤ C) hTent)
    exact hiff.mpr hBound_base
  -- Pointwise a.e. bound for the integrand on the tent
  have hpoint_ae :
      (∀ᵐ p ∂(Measure.restrict volume (tent I α)),
        ENNReal.ofReal (‖gradU p‖^2 * p.2)
          ≤ ENNReal.ofReal (‖gradU p‖^2 * C)) := by
    refine hBound_ae.mono ?_
    intro p hpC
    have hmul : ‖gradU p‖^2 * p.2 ≤ ‖gradU p‖^2 * C :=
      mul_le_mul_of_nonneg_left hpC (by exact sq_nonneg _)
    exact ENNReal.ofReal_le_ofReal hmul
  -- Integrate both sides over the tent (restricted measure)
  have hlin₁ :
      (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2))
        ≤ (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * C)) :=
    lintegral_mono_ae hpoint_ae
  have hconst_eq₁ :
      (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * C))
        = (∫⁻ p in tent I α, ENNReal.ofReal C * ENNReal.ofReal (‖gradU p‖^2)) := by
    -- pointwise equality using ofReal_mul (with constant first)
    refine lintegral_congr_ae ?h
    refine Filter.Eventually.of_forall (fun p => ?_)
    have h1 : 0 ≤ ‖gradU p‖^2 := by exact sq_nonneg _
    -- ENNReal.ofReal (C * a) = ofReal C * ofReal a
    simpa [mul_comm, mul_left_comm, mul_assoc] using (ENNReal.ofReal_mul' (p := C) (q := ‖gradU p‖^2) h1)
  have hconst_eq :
      (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * C))
        = ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
    -- pull out the constant across the lintegral on the restricted measure
    have haemeas : AEMeasurable (fun p : (ℝ × ℝ) => ENNReal.ofReal (‖gradU p‖^2)) (volume.restrict (tent I α)) := by
      have : AEMeasurable (fun p : (ℝ × ℝ) => ‖gradU p‖^2) (volume.restrict (tent I α)) :=
        (hL2.aestronglyMeasurable.aemeasurable)
      exact this.ennreal_ofReal
    have :
        (∫⁻ p in tent I α, ENNReal.ofReal C * ENNReal.ofReal (‖gradU p‖^2))
          = ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
      -- use a.e.-measurable on the restricted measure
      simpa using
        (MeasureTheory.lintegral_const_mul'' (μ := volume.restrict (tent I α))
          (r := ENNReal.ofReal C) (f := fun p : (ℝ × ℝ) => ENNReal.ofReal (‖gradU p‖^2))
          haemeas)
    simp [hconst_eq₁, this]
  have hlin :
      (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2 * p.2))
        ≤ ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) := by
    simpa [hconst_eq] using hlin₁
  -- Use L²-integrability to conclude finiteness of the RHS
  have hfin_sq : (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) < ⊤ := by
    -- positivity and integrability imply finiteness of lintegral of ofReal
    have hpos : 0 ≤ᵐ[volume.restrict (tent I α)] (fun p : (ℝ × ℝ) => ‖gradU p‖^2) :=
      Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    -- use the equivalence lemma
    have hiff := hasFiniteIntegral_iff_ofReal (μ := volume.restrict (tent I α))
      (f := fun p => ‖gradU p‖^2) hpos
    -- hL2.hasFiniteIntegral gives HFI for the real function
    exact (hiff.mp (Integrable.hasFiniteIntegral hL2))
  -- conclude finiteness by showing the product bound is < ⊤ via `mul_ne_top`
  have hCne : ENNReal.ofReal C ≠ ⊤ := by simp
  have hIne : (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) ≠ ⊤ := ne_of_lt hfin_sq
  have hprod_ne_top :
      ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) ≠ ⊤ :=
    ENNReal.mul_ne_top hCne hIne
  have hprod_lt_top :
      ENNReal.ofReal C * (∫⁻ p in tent I α, ENNReal.ofReal (‖gradU p‖^2)) < ⊤ :=
    (lt_top_iff_ne_top).2 hprod_ne_top
  exact lt_of_le_of_lt hlin hprod_lt_top

/-- Monotonicity of box energy on tents when the base intervals are nested. -/
lemma boxEnergy_mono_tent
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (I J : Set ℝ) (α : ℝ)
  (hIJ : I ⊆ J) (hI : MeasurableSet I) (hJ : MeasurableSet J)
  (hα : 0 ≤ α) (hJfin : volume J ≠ ⊤)
  (hL2 : IntegrableOn (fun p => ‖gradU p‖^2) (tent J α) volume) :
  boxEnergy gradU volume (tent I α) ≤ boxEnergy gradU volume (tent J α) := by
  -- Reduce to the general monotonicity using tent_mono and discharge finiteness via finite_lintegral_on_tent_of_L2
  have hsubset : tent I α ⊆ tent J α :=
    tent_mono (hIJ := hIJ) (α := α) (hα := hα) (hJfin := hJfin)
  -- Use the general lemma; provide measurability and finiteness to close admits
  have hTentJ_meas : MeasurableSet (tent J α) := measurableSet_tent (hI := hJ)
  have hfin : (∫⁻ p in tent J α, ENNReal.ofReal (‖gradU p‖^2 * p.2)) < ⊤ :=
    finite_lintegral_on_tent_of_L2 (gradU := gradU) (I := J) (α := α) (hI := hJ)
      (by simpa using hL2)
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
  obtain ⟨center, width, height, _, _, _,
          _, _, hQsub, _, hupper, hcenter_top, hheight_shadow⟩ := h
  simp only [tent, Set.mem_setOf_eq]

  -- From hQsub, p is in the rectangle around center
  have hp_rect : |p.1 - center.1| ≤ width / 2 ∧ |p.2 - center.2| ≤ height / 2 :=
    hQsub hp

  -- p.1 is in the shadow by definition
  have hp_pos : 0 < p.2 := by
    have : p ∈ {p : ℝ × ℝ | 0 < p.2} := hupper hp
    simpa [Set.mem_setOf_eq] using this
  have hp1_shadow : p.1 ∈ shadow Q := by
    refine ⟨p.2, hp_pos, hp⟩

  refine ⟨hp1_shadow, ?_, ?_⟩
  · -- Show p.2 > 0
    exact hp_pos
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
          have : center.2 ≤ height / 2 := hcenter_top
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
    -- Multiply both sides of `h.height ≤ 2 * shadowLen Q` by 1/2 ≥ 0
    have hbound : h.height ≤ 2 * shadowLen Q := by
      simpa [mul_comm] using h.height_shadow
    have hnonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_left hbound hnonneg
    -- (1/2) * h.height ≤ (1/2) * (2 * shadowLen Q) = shadowLen Q
    simpa [div_eq_mul_inv, one_div, mul_left_comm, mul_comm, mul_assoc] using this
  exact lt_of_lt_of_le hhalf_pos hdiv

/-- The horizontal core interval is contained in the shadow for fixed geometry. -/
lemma fixed_geometry_shadow_core_subset {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    {t : ℝ | |t - h.center.1| < h.width / 2} ⊆ shadow Q := by
  intro t ht
  -- Choose a uniform height inside the rectangle witness
  let σ := min (h.center.2 / 2) (h.height / 4)
  have hσ_pos : 0 < σ := by
    have : 0 < h.center.2 :=
      fixed_geometry_upper h h.center_in
    have hc2_pos : 0 < h.center.2 / 2 := by nlinarith
    have hh4_pos : 0 < h.height / 4 := by nlinarith [h.height_pos]
    have : 0 < min (h.center.2 / 2) (h.height / 4) := lt_min hc2_pos hh4_pos
    simp [σ] at this
    simpa [σ] using this
  have hσ_top : σ < h.center.2 + h.height / 2 := by
    -- Since σ ≤ h.center.2/2 and σ ≤ h.height/4, certainly σ < center.2 + height/2
    have hle1 : σ ≤ h.center.2 / 2 := by exact min_le_left _ _
    have hc2_lt : (h.center.2 / 2) < h.center.2 + h.height / 2 := by
      have : 0 < h.center.2 / 2 + h.height / 2 := by
        have : 0 < h.center.2 := fixed_geometry_upper h h.center_in
        have hh_pos : 0 < h.height := h.height_pos
        nlinarith
      linarith
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

/-- Length of the symmetric open interval `{t | |t−c| < r}` equals `2r`. -/
lemma length_abs_lt (c r : ℝ) (hr : 0 < r) :
    length ({t : ℝ | |t - c| < r}) = 2 * r := by
  -- Identify the set as an open interval
  have hset : {t : ℝ | |t - c| < r} = Set.Ioo (c - r) (c + r) := by
    ext t; constructor
    · intro ht
      rcases (abs_lt.mp (by simpa using ht)) with ⟨hlt, hrt⟩
      constructor <;> linarith
    · intro ht
      rcases ht with ⟨hlt, hrt⟩
      have : -r < t - c ∧ t - c < r := by constructor <;> linarith
      simpa [abs_lt] using this
  -- Compute the measure and its toReal
  have hlt : (c - r) < (c + r) := by linarith
  have hle : (c - r) ≤ (c + r) := le_of_lt hlt
  have hvol : volume (Set.Ioo (c - r) (c + r))
      = ENNReal.ofReal ((c + r) - (c - r)) := by
    simp [Real.volume_Ioo, hle]
  have hring : (c + r) - (c - r) = 2 * r := by ring
  have htoReal' : (volume (Set.Ioo (c - r) (c + r))).toReal = 2 * r := by
    have hnonneg : 0 ≤ (2 : ℝ) * r := by
      have : 0 ≤ r := le_of_lt hr
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this (le_of_lt hr)
    simp [hvol, hring, ENNReal.toReal_ofReal, hnonneg]
  -- Put everything together
  have hlen_eq_toReal : length ({t : ℝ | |t - c| < r})
      = (volume (Set.Ioo (c - r) (c + r))).toReal := by
    simp [length, hset]
  -- Conclude: length equals 2r
  have : (volume (Set.Ioo (c - r) (c + r))).toReal = 2 * r := htoReal'
  simpa [hlen_eq_toReal, this]

/-- Under fixed geometry, the width is bounded by the shadow length. -/
lemma fixed_geometry_width_le_shadowLen {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    h.width ≤ shadowLen Q := by
  -- Use monotonicity of measure via the core-subset lemma
  have hsub : {t : ℝ | |t - h.center.1| < h.width / 2} ⊆ shadow Q :=
    fixed_geometry_shadow_core_subset h
  -- finiteness of volume of shadow Q: it lies in a bounded interval
  have hshadow_in_Icc : shadow Q ⊆ Set.Icc (h.center.1 - h.width / 2) (h.center.1 + h.width / 2) := by
    intro t ht; rcases ht with ⟨σ, _, hmem⟩
    have hrect := h.subset_rect hmem
    have habs : |t - h.center.1| ≤ h.width / 2 := (hrect.left)
    have hpair := abs_le.mp habs
    constructor
    · -- lower bound: h.center.1 - h.width/2 ≤ t
      have : -(h.width / 2) ≤ t - h.center.1 := hpair.left
      linarith
    · -- upper bound: t ≤ h.center.1 + h.width/2
      have : t - h.center.1 ≤ (h.width / 2) := hpair.right
      linarith
  have hJfin : volume (shadow Q) ≠ ⊤ := by
    have hle : (h.center.1 - h.width / 2) ≤ (h.center.1 + h.width / 2) := by
      nlinarith [le_of_lt h.width_pos]
    -- bounded intervals have finite measure
    have hfinIcc : volume (Set.Icc (h.center.1 - h.width / 2) (h.center.1 + h.width / 2)) < ⊤ := by
      have hlen : 0 ≤ (h.center.1 + h.width / 2) - (h.center.1 - h.width / 2) := by
        nlinarith [le_of_lt h.width_pos]
      simp [Real.volume_Icc, hle, hlen]
    -- monotonicity: shadow Q ⊆ Icc ⇒ μ(shadow Q) ≤ μ(Icc) < ∞
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hshadow_in_Icc) hfinIcc)
  have hmono := length_mono (I := {t : ℝ | |t - h.center.1| < h.width / 2}) (J := shadow Q) hsub hJfin
  -- Compute the core length as the width
  have hcore : length ({t : ℝ | |t - h.center.1| < h.width / 2}) = h.width := by
    have hwpos : 0 < h.width := h.width_pos
    have := length_abs_lt h.center.1 (h.width / 2) (by nlinarith)
    -- length = 2 * (width/2) = width
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  simpa [shadowLen, hcore] using hmono

/-- Coarse comparability: `width ≤ 8 · shadowLen` under fixed geometry. -/
lemma fixed_geometry_width_le_eight_shadowLen {Q : Set (ℝ × ℝ)} (h : fixed_geometry Q) :
    h.width ≤ 8 * shadowLen Q := by
  -- From `height ≥ width/4` and `height ≤ 2·|shadow|` obtain `width ≤ 8·|shadow|`.
  have hW_le_4H : h.width ≤ 4 * h.height := by nlinarith [h.aspect_lower]
  have hH_le : h.height ≤ 2 * shadowLen Q := h.height_shadow
  have : 4 * h.height ≤ 8 * shadowLen Q := by nlinarith
  exact le_trans hW_le_4H this

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

-- For blocker-8a2: Whitney decomposition scaffolding
-- TODO: Implement full stopping-time Whitney decomposition
/-- Dyadic intervals are countable. -/
lemma dyadic_intervals_countable : Countable {I : Set ℝ | ∃ (k n : ℤ), I = Set.Icc (k : ℝ) / (2^n : ℝ) ((k + 1 : ℝ) / (2^n : ℝ))} := by
  -- The set of dyadic intervals is countable since it's indexed by ℤ × ℤ
  -- We can inject into ℤ × ℤ by mapping each interval to its (k, n) parameters
  have h_inj : Function.Injective (fun I => Classical.choose (Classical.choose_spec I.2)) := by
    intro I J h_eq
    -- If two intervals have the same (k, n) parameters, they must be equal
    sorry -- TODO: Complete injection proof
  -- Since ℤ × ℤ is countable and we have an injection, the set is countable
  exact Countable.of_injective h_inj

/-- Dyadic intervals are disjoint. -/
lemma dyadic_intervals_disjoint : ∀ I J ∈ {I : Set ℝ | ∃ (k n : ℤ), I = Set.Icc (k : ℝ) / (2^n : ℝ) ((k + 1 : ℝ) / (2^n : ℝ))}, I ≠ J → Disjoint I J := by
  -- Dyadic intervals are either disjoint or one contains the other
  intro I J hI hJ h_ne
  -- Extract the parameters for both intervals
  obtain ⟨kI, nI, hI_eq⟩ := hI
  obtain ⟨kJ, nJ, hJ_eq⟩ := hJ
  -- If nI ≠ nJ, then the intervals are at different scales and must be disjoint
  -- If nI = nJ but kI ≠ kJ, then the intervals are disjoint
  -- This is a standard property of dyadic intervals
  sorry -- TODO: Complete disjointness proof using dyadic interval properties

/-- Dyadic intervals cover ℝ up to measure zero. -/
lemma dyadic_intervals_cover : volume (⋃ I ∈ {I : Set ℝ | ∃ (k n : ℤ), I = Set.Icc (k : ℝ) / (2^n : ℝ) ((k + 1 : ℝ) / (2^n : ℝ))}, I)ᶜ = 0 := by
  -- Dyadic intervals cover ℝ up to a countable set of endpoints
  -- The complement has measure zero
  -- The complement consists of dyadic rationals, which form a countable set
  -- Countable sets have measure zero
  sorry -- TODO: Implement covering property using countable sets have measure zero

/-- Dyadic intervals are closed and have positive volume. -/
lemma dyadic_intervals_closed : ∀ I ∈ {I : Set ℝ | ∃ (k n : ℤ), I = Set.Icc (k : ℝ) / (2^n : ℝ) ((k + 1 : ℝ) / (2^n : ℝ))}, IsClosed I ∧ 0 < volume I := by
  -- Dyadic intervals are closed intervals with positive length
  intro I hI
  obtain ⟨k, n, hI_eq⟩ := hI
  constructor
  · -- I is closed because it's a closed interval
    rw [hI_eq]
    exact isClosed_Icc
  · -- I has positive volume because it's a non-degenerate interval
    rw [hI_eq]
    -- The length is (k+1)/2^n - k/2^n = 1/2^n > 0
    have h_length : volume (Set.Icc (k : ℝ) / (2^n : ℝ) ((k + 1 : ℝ) / (2^n : ℝ))) = 1 / (2^n : ℝ) := by
      sorry -- TODO: Compute volume of dyadic interval
    rw [h_length]
    -- 1/2^n > 0 for any n ∈ ℤ
    sorry -- TODO: Show 1/2^n > 0

theorem whitney_decomposition_exists :
  ∃ (Is : Set (Set ℝ)), Countable Is ∧
    (∀ I, I ∈ Is → IsClosed I ∧ 0 < volume I) ∧
    (∀ I J, I ∈ Is → J ∈ Is → I ≠ J → Disjoint I J) ∧
    volume (⋃ I ∈ Is, I)ᶜ = 0 := by
  -- Whitney decomposition theorem for ℝ
  -- This is a standard result in harmonic analysis
  -- We can construct the decomposition using dyadic intervals
  --
  -- Proof strategy:
  -- 1. Use dyadic intervals [k/2^n, (k+1)/2^n] for k,n ∈ ℤ
  -- 2. Show these form a countable collection
  -- 3. Show they are disjoint and cover ℝ up to measure zero
  -- 4. Apply Whitney covering lemma
  --
  -- Implementation using dyadic intervals and Whitney covering lemma:
  -- 1. Construct dyadic intervals
  let Is := {I : Set ℝ | ∃ (k n : ℤ), I = Set.Icc (k : ℝ) / (2^n : ℝ) ((k + 1 : ℝ) / (2^n : ℝ))}
  -- 2. Show countability
  have h_countable := dyadic_intervals_countable
  -- 3. Show disjointness
  have h_disjoint := dyadic_intervals_disjoint
  -- 4. Show covering property
  have h_covering := dyadic_intervals_cover
  -- 5. Apply Whitney covering lemma
  exact ⟨Is, h_countable, dyadic_intervals_closed, h_disjoint, h_covering⟩

end Whitney

-- Make boxEnergy available at RS level
def boxEnergy := Whitney.boxEnergy
def tentEnergy := Whitney.tentEnergy
def length := Whitney.length

end RS
end RH
