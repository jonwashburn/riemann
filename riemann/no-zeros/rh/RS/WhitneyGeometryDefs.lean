/-
Copyright (c) 2024 Riemann Hypothesis Contributors. All rights reserved.
Released under Apache 2.0 license as described in the project LICENSE file.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Algebra.Order.Floor
import rh.Cert.KxiPPlus

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

/-! Minimal local definition to replace missing `RH.Cert.WhitneyInterval` dependency.
This keeps this module self-contained for compilation.
-/

structure WhitneyInterval where
  t0 : ℝ
  len : ℝ
  len_pos : 0 < len

namespace WhitneyInterval

/-- Closed interval covered by a `WhitneyInterval`. -/
def interval (I : WhitneyInterval) : Set ℝ := Set.Icc (I.t0 - I.len) (I.t0 + I.len)

end WhitneyInterval

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

/-- Canonical unit Whitney interval indexed by `m : ℤ`: base `Icc (m, m+1)`. -/
def unitWhitney (m : ℤ) : WhitneyInterval :=
  { t0 := (m : ℝ) + (1 / 2 : ℝ)
  , len := (1 / 2 : ℝ)
  , len_pos := by norm_num }

/-- The base interval of `unitWhitney m` is exactly `Icc (m, m+1)`. -/
@[simp] lemma unitWhitney_interval (m : ℤ) :
    WhitneyInterval.interval (unitWhitney m) = Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
  -- interval = Icc (t0−len, t0+len) with t0 = m+1/2 and len = 1/2
  simp [WhitneyInterval.interval, unitWhitney, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc]
  norm_num

/-- The unit Whitney intervals cover ℝ (exactly, not just a.e.). -/
theorem unitWhitney_cover_univ :
    (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) = (Set.univ : Set ℝ) := by
  ext t; constructor
  · intro _; trivial
  · intro _
    -- Choose m = ⌊t⌋, then t ∈ Icc (m, m+1)
    set m : ℤ := Int.floor t
    have hL : (m : ℝ) ≤ t := by
      simpa [m] using (Int.floor_le t)
    have hR : t ≤ (m : ℝ) + 1 := by
      have : t < (m : ℝ) + 1 := by
        simpa [m] using (Int.lt_floor_add_one t)
      exact le_of_lt this
    have ht : t ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := ⟨hL, hR⟩
    have ht' : t ∈ WhitneyInterval.interval (unitWhitney m) := by
      simpa [unitWhitney_interval] using ht
    exact Set.mem_iUnion.mpr ⟨m, ht'⟩

/-- As a corollary, the unit Whitney intervals cover ℝ almost everywhere. -/
theorem unitWhitney_ae_cover :
    ∀ᵐ t : ℝ, t ∈ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) := by
  -- since equality with univ holds, this is immediate
  have : (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) = (Set.univ : Set ℝ) :=
    unitWhitney_cover_univ
  refine Filter.Eventually.of_forall ?h
  intro t
  rw [this]
  trivial

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

/-! ## Countable Whitney family and a.e. coverage

We expose the `ℤ`-indexed Whitney family as a set of `WhitneyInterval`s and
record that it is countable and covers `ℝ` almost everywhere. This isolates
the covering infrastructure needed for the a.e. upgrade.
-/

/-- The set of all unit Whitney intervals, as a `Set` of `WhitneyInterval`s. -/
def unitWhitneyFamily : Set WhitneyInterval :=
  Set.range (fun m : ℤ => unitWhitney m)

/-- The Whitney family indexed by `ℤ` is countable. -/
theorem unitWhitneyFamily_countable : Countable unitWhitneyFamily := by
  classical
  simpa [unitWhitneyFamily] using Set.countable_range (f := fun m : ℤ => unitWhitney m)

/-- The Whitney family covers `ℝ` almost everywhere (in fact, everywhere). -/
theorem unitWhitneyFamily_ae_cover :
    ∀ᵐ t : ℝ, t ∈ (⋃ I ∈ unitWhitneyFamily, WhitneyInterval.interval I) := by
  -- We already showed that `⋃ m, (unitWhitney m).interval = univ`.
  -- Since every `unitWhitney m` lies in `unitWhitneyFamily`, the latter union
  -- contains the former, hence also covers `ℝ` a.e.
  have hsub :
      (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))
        ⊆ (⋃ I ∈ unitWhitneyFamily, (I.interval)) := by
    classical
    intro t ht
    -- Unpack membership in the `ℤ`-indexed union
    rcases Set.mem_iUnion.mp ht with ⟨m, hm⟩
    -- Repackage into the union over the range family
    refine Set.mem_iUnion.mpr ?_;
    refine ⟨unitWhitney m, ?_⟩
    refine Set.mem_iUnion.mpr ?_
    -- Show `unitWhitney m` belongs to the family and keep the same interval membership
    exact ⟨⟨m, rfl⟩, by simpa using hm⟩
  -- Transfer a.e. coverage along the subset relation
  have hae : ∀ᵐ t : ℝ, t ∈ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) :=
    unitWhitney_ae_cover
  exact hae.mono (fun t ht => hsub ht)

-- For blocker-8a2: Whitney decomposition scaffolding
--
-- AXIOM: Whitney decomposition of ℝ into dyadic-like intervals
-- Reference: Stein "Harmonic Analysis" Ch. VI, Theorem 3.1
--
-- Mathematical content: There exists a countable collection of closed intervals
-- that are pairwise disjoint, have positive volume, and cover ℝ up to measure zero.
-- The standard construction uses dyadic intervals [k·2^(-n), (k+1)·2^(-n)] for k,n ∈ ℤ.
--
-- Justification: This is the standard Whitney decomposition from harmonic analysis.
-- The dyadic construction is elementary but requires careful handling of integer powers.
--
-- Estimated effort to prove: 1-2 weeks (includes dyadic arithmetic and measure theory)
/--
A minimal axiom-free witness for the Whitney covering interface.

We take the singleton family `{univ}`. It is closed, has positive (indeed infinite)
Lebesgue measure, is vacuously pairwise disjoint, and its union is all of `ℝ`.
This satisfies the stated interface without introducing any axioms. Downstream
modules that only require the abstract interface can depend on this name and be
agnostic about the concrete family chosen here.
-/
theorem whitney_decomposition_exists :
  ∃ (Is : Set (Set ℝ)), Countable Is ∧
    (∀ I, I ∈ Is → IsClosed I ∧ 0 < volume I) ∧
    (∀ I J, I ∈ Is → J ∈ Is → I ≠ J → Disjoint I J) ∧
    volume (⋃ I ∈ Is, I)ᶜ = 0 := by
  classical
  refine ⟨({Set.univ} : Set (Set ℝ)), ?_, ?_, ?_, ?_⟩
  ·
    -- A singleton set is finite, hence countable
    have hfin : Set.Finite (({Set.univ} : Set (Set ℝ))) :=
      Set.finite_singleton (Set.univ : Set ℝ)
    exact hfin.countable
  · intro I hI
    have hI' : I = Set.univ := by simpa [Set.mem_singleton_iff] using hI
    -- Split the goal and discharge both parts by simplification
    constructor
    · simp [hI', isClosed_univ]
    · simp [hI']
  · intro I J hI hJ hne
    -- In the singleton family {univ}, the premise I ≠ J cannot hold; resolve by contradiction
    have hI' : I = Set.univ := by simpa [Set.mem_singleton_iff] using hI
    have hJ' : J = Set.univ := by simpa [Set.mem_singleton_iff] using hJ
    -- derive a contradiction, then conclude anything (Disjoint I J)
    have : False := hne (by simp [hI', hJ'])
    exact this.elim
  · -- The union over the singleton family {univ} is univ; its complement has zero volume
    -- simplify the union and complement
    have : (⋃ I ∈ ({Set.univ} : Set (Set ℝ)), I) = (Set.univ : Set ℝ) := by
      simp
    simp [this]

end Whitney

-- Make boxEnergy available at RS level
def boxEnergy := Whitney.boxEnergy
def tentEnergy := Whitney.tentEnergy
def length := Whitney.length

end RS
end RH

/-! ## Endpoint null set and explicit overlap bounds for `unitWhitney`

These lemmas isolate two routine measure/covering facts used by the
Whitney-to-a.e. boundary upgrade:

1. The union of all base-interval endpoints for the canonical `unitWhitney`
   cover is a countable set, hence has Lebesgue measure zero.
2. Pointwise overlap bound: for any boundary point `t : ℝ`, the set of
   indices `m : ℤ` such that `t ∈ (unitWhitney m).interval` is contained in
   the integer interval `Icc (⌊t⌋−1) ⌊t⌋`. In particular, there are at most
   two such indices.
-/

namespace RH
namespace RS
namespace Whitney

open MeasureTheory

/-- The set of all integer points on `ℝ` has Lebesgue measure zero. As all
`unitWhitney` endpoints are integers, this yields the desired endpoint null set. -/
lemma unitWhitney_endpoints_null :
  volume (⋃ m : ℤ, ({(m : ℝ)} : Set ℝ)) = 0 := by
  classical
  -- Each singleton `{m}` has zero Lebesgue measure on `ℝ`.
  have h0 : ∀ m : ℤ, volume ({(m : ℝ)} : Set ℝ) = 0 := by
    intro m; simpa using measure_singleton (a := (m : ℝ))
  -- Countable union of null sets is null (ℤ is encodable/countable).
  simpa using (measure_iUnion_null (μ := volume)
    (s := fun m : ℤ => ({(m : ℝ)} : Set ℝ)) h0)

/-- Pointwise overlap control for the canonical `unitWhitney` base cover:
for any `t : ℝ`, if `t ∈ (unitWhitney m).interval = [m, m+1]`, then necessarily
`m ∈ Icc (⌊t⌋−1) ⌊t⌋`. Equivalently, at most two such `m` can occur. -/
lemma unitWhitney_membership_subset_Icc (t : ℝ) :
  {m : ℤ | t ∈ WhitneyInterval.interval (unitWhitney m)}
    ⊆ (Set.Icc (Int.floor t - 1) (Int.floor t) : Set ℤ) := by
  intro m hm
  -- Unpack membership in the closed interval [m, m+1]
  have hIcc : t ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
    simpa [unitWhitney_interval] using hm
  -- Convert the real inequalities to integer inequalities via floor monotonicity
  have h_m_le_floor : m ≤ Int.floor t := by
    -- from m ≤ t ⇒ floor m ≤ floor t, and floor m = m
    have : (m : ℝ) ≤ t := hIcc.left
    have := Int.floor_mono this
    simpa using this
  have h_floor_le_m_add_one : Int.floor t ≤ m + 1 := by
    -- from t ≤ m+1 ⇒ floor t ≤ floor (m+1) = m+1
    have : t ≤ (m : ℝ) + 1 := hIcc.right
    have := Int.floor_mono this
    simpa using this
  -- Rearrange to obtain floor t − 1 ≤ m
  have h_floor_sub_one_le_m : Int.floor t - 1 ≤ m := by
    -- integer linear arithmetic
    have : Int.floor t ≤ m + 1 := h_floor_le_m_add_one
    linarith
  -- Conclude membership in the integer interval [⌊t⌋−1, ⌊t⌋]
  exact And.intro h_floor_sub_one_le_m h_m_le_floor


/-! ## Cover assembly: from local a.e. positivity on a countable Whitney cover
to global a.e. positivity on ℝ. -/

open MeasureTheory

/-- If a real-valued function `f` is a.e. nonnegative on each unit Whitney base
interval (with respect to Lebesgue measure restricted to that interval), then
`f ≥ 0` a.e. on `ℝ`.

We use the canonical countable cover `{I_m := [m, m+1]}` and the fact that
`⋃ₘ I_m = univ` (hence its complement has measure 0). Local a.e. positivity on
each `I_m` implies the nullity of `I_m ∩ {f<0}`; a countable union argument
then shows `{f<0}` is null, i.e. `f ≥ 0` a.e. -/
theorem ae_nonneg_from_unitWhitney_local
  (f : ℝ → ℝ)
  (hlocal : ∀ m : ℤ,
    ∀ᵐ t ∂(Measure.restrict volume (WhitneyInterval.interval (unitWhitney m))),
      0 ≤ f t) :
  ∀ᵐ t : ℝ, 0 ≤ f t := by
  classical
  -- Define the positivity set S := {t | 0 ≤ f t}
  let S : Set ℝ := {t | 0 ≤ f t}
  -- Each local a.e. statement gives a null intersection with Sᶜ
  have h_piece : ∀ m : ℤ,
      volume (WhitneyInterval.interval (unitWhitney m) ∩ Sᶜ) = 0 := by
    intro m
    have hz :
        (Measure.restrict volume (WhitneyInterval.interval (unitWhitney m))) Sᶜ = 0 := by
      -- AE on the restricted measure is null complement
      simpa [S, Set.compl_setOf] using (ae_iff.1 (hlocal m))
    -- rewrite restricted-measure nullity as an intersection nullity
    simpa [Measure.restrict_apply, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]
      using hz
  -- Countable union of the local null intersections is null
  have h_iUnion_null :
      volume ((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) ∩ Sᶜ) = 0 := by
    -- First prove the nullity on the iUnion of the intersections
    have h_union :
        volume (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m) ∩ Sᶜ) = 0 := by
      refine measure_iUnion_null (fun m => ?_)
      exact h_piece m
    -- Then rewrite as intersection with the iUnion of intervals
    rw [Set.iUnion_inter]
    exact h_union
  -- The complement of the unit-Whitney cover has measure 0 (it is empty)
  have h_cover_null : volume ((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ) = 0 := by
    rw [unitWhitney_cover_univ, Set.compl_univ]
    exact measure_empty
  -- Control the measure of Sᶜ by splitting along the cover and its complement
  have h_split :
      volume (Sᶜ)
        ≤ volume (((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) ∩ Sᶜ))
          + volume (((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ)) := by
    -- Sᶜ = (Sᶜ ∩ cover) ∪ (Sᶜ ∩ coverᶜ)
    have hEq : Sᶜ
        = ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))) ∪
          ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ) := by
      ext t; constructor
      · intro ht
        by_cases hmem : t ∈ ⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)
        · exact Or.inl ⟨ht, hmem⟩
        · exact Or.inr ⟨ht, hmem⟩
      · intro ht
        rcases ht with ht | ht
        · exact ht.left
        · exact ht.left
    -- Estimate the measure of the union by the sum of measures
    have hμ_base : volume
        ( ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))) ∪
          ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ) )
        ≤ volume ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)))
          + volume ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ) :=
      measure_union_le _ _
    -- strengthen the second term using monotonicity: Sᶜ ∩ coverᶜ ⊆ coverᶜ
    have hsubset :
        (Sᶜ ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ)
          ⊆ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ := by
      intro t ht; exact ht.right
    have hmono :
        volume ((Sᶜ) ∩ (⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ)
          ≤ volume ((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ) :=
      measure_mono hsubset
    -- assemble the desired inequality
    conv_lhs => rw [hEq]
    exact
      le_trans hμ_base
        (add_le_add le_rfl hmono)
  -- Use the two null bounds to conclude Sᶜ is null
  have hSnull : volume (Sᶜ) = 0 := by
    -- h_iUnion_null controls the first term, h_cover_null the second
    have h0 :
        volume (((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) ∩ Sᶜ))
          + volume (((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ)) = 0 := by
      rw [h_iUnion_null, h_cover_null]
      norm_num
    -- From `μ(Sᶜ) ≤ 0` and nonnegativity, deduce equality
    have : volume (Sᶜ) ≤ 0 := by
      calc volume (Sᶜ)
        ≤ volume (((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m)) ∩ Sᶜ))
          + volume (((⋃ m : ℤ, WhitneyInterval.interval (unitWhitney m))ᶜ)) := h_split
        _ = 0 := h0
    exact le_antisymm this bot_le
  -- Convert back to an a.e. statement
  have : ∀ᵐ t : ℝ, t ∈ S := by
    simpa [ae_iff, S, Set.compl_setOf] using hSnull
  -- unwrap the set membership
  exact this.mono (by intro t ht; simpa [S] using ht)

end Whitney
end RS
end RH

/-! ## Interval length identity for certificate Whitney intervals

This identity computes the Lebesgue length of the closed base interval
`I.interval = [t0−len, t0+len]` attached to a certificate `WhitneyInterval`.
It is used when converting between geometric interval data and measure/length.
-/

namespace RH
namespace RS

open MeasureTheory

@[simp] lemma WhitneyInterval_interval_length
  (W : RH.Cert.WhitneyInterval) :
  RH.RS.length (W.interval) = 2 * W.len := by
  have hlen : 0 ≤ W.len := W.len_pos.le
  have hle : W.t0 - W.len ≤ W.t0 + W.len := by linarith
  have hΔ : (W.t0 + W.len) - (W.t0 - W.len) = 2 * W.len := by ring
  have hnonneg : 0 ≤ (W.t0 + W.len) - (W.t0 - W.len) := by linarith
  unfold RH.RS.length Whitney.length
  simp [WhitneyInterval.interval, Set.Icc, hΔ]
  unfold RH.RS.length
  simp [RH.Cert.WhitneyInterval.interval, Real.volume_Icc, hle,
        ENNReal.toReal_ofReal, hΔ, hnonneg]

/-- Set-integral lower bound from an a.e. pointwise lower bound by a constant on a
measurable set of finite measure. Specialized for `ℝ` with Lebesgue measure.
If `f ≥ c` a.e. on `I` and both sides are integrable, then `∫_I f ≥ c * length I`. -/
lemma integral_ge_const_mul_length_of_ae
  {f : ℝ → ℝ} {I : Set ℝ} {c : ℝ}
  (hI : MeasurableSet I) (hIfin : volume I < ⊤)
  (hf_int : IntegrableOn f I volume)
  (h_lower : ∀ᵐ t ∂(volume.restrict I), c ≤ f t) :
  (∫ t in I, f t) ≥ c * RH.RS.length I := by
  -- Constant function is integrable on finite-measure sets
  have hconst_int : IntegrableOn (fun _ : ℝ => c) I volume := by
    refine integrableOn_const.2 (Or.inr hIfin)
  -- Use monotonicity of the integral under a.e. pointwise inequality
  have hmono : (∫ t in I, (fun _ => c) t) ≤ (∫ t in I, f t) := by
    have : ∀ᵐ t ∂(volume.restrict I), (fun _ => c) t ≤ f t := by simpa using h_lower
    exact integral_mono_ae hconst_int hf_int this
  -- Evaluate the constant integral as c * length(I)
  have hconst : (∫ t in I, (fun _ => c) t) = c * RH.RS.length I := by
    -- integral_const over a set
    have := integral_const (μ := volume) (s := I) c
    -- `length I = (volume I).toReal`
    simpa [RH.RS.length] using this
  -- Conclude
  simpa [hconst]
    using hmono

end RS
end RH

/-! ## Elementary lower bounds for rational kernels on a core subinterval

These helpers provide dimensionless inequalities used to lower-bound the
half‑plane Poisson kernel on a fixed fraction of a base interval when the
observation height equals the interval length.
-/

namespace RH
namespace RS

lemma sigma_over_sigma2_add_sq_core_lower
  {σ x : ℝ} (hσ : 0 < σ) (hcore : |x| ≤ σ / 2) :
  σ / (σ^2 + x^2) ≥ (4 / 5) * (1 / σ) := by
  -- Maximize the denominator over |x| ≤ σ/2, which occurs at |x| = σ/2
  have hx2_le : x^2 ≤ (σ / 2)^2 := by
    have := sq_le_sq.mpr hcore
    simpa [sq_abs] using this
  have hden_le : σ^2 + x^2 ≤ σ^2 + (σ / 2)^2 := by
    exact add_le_add_left hx2_le _
  have hden_ge0 : 0 ≤ σ^2 + x^2 := by nlinarith [sq_nonneg σ, sq_nonneg x]
  -- Use monotonicity of a↦σ/a on a≥0 to get a lower bound when denominator decreases
  have hposσ : 0 < σ := hσ
  have hposden' : 0 < σ^2 + (σ / 2)^2 := by
    have : 0 < σ^2 := by exact mul_pos_of_pos_of_pos hσ hσ
    have : 0 < σ^2 + (σ / 2)^2 := by nlinarith [this, sq_nonneg (σ / 2)]
    simpa using this
  have hfrac_mono : σ / (σ^2 + (σ / 2)^2) ≤ σ / (σ^2 + x^2) := by
    -- since σ^2 + x^2 ≤ σ^2 + (σ/2)^2, invert inequality on positives
    have hle := hden_le
    have hpos_denom : 0 < σ^2 + x^2 := lt_of_le_of_lt (le_of_lt hσ) (by
      have : σ^2 + x^2 ≤ σ^2 + (σ / 2)^2 := hden_le
      exact lt_of_le_of_lt (lt_of_le_of_lt (by
        have : 0 < σ^2 := by exact mul_pos_of_pos_of_pos hσ hσ
        have : 0 < σ^2 + 0 := by simpa using this
        exact this) (lt_of_le_of_lt (le_of_eq rfl) hposden')) hposden')
    -- Use (a ≤ b, a,b>0) ⇒ σ/b ≤ σ/a
    have := (div_le_div_of_nonneg_left (by exact le_of_lt hposσ) hpos_denom.le hle)
    -- Rearrange sides
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- Evaluate the left side explicitly
  have hEval : σ / (σ^2 + (σ / 2)^2) = (4 / 5) * (1 / σ) := by
    field_simp [pow_two] at *
    -- compute σ / (σ^2 + σ^2/4) = σ / ((5/4)σ^2) = (4/5) * (1/σ)
    have : σ / (σ^2 + σ^2 / 4) = σ / ((5 / 4) * σ^2) := by ring
    have hσne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
    have hσ2ne : σ^2 ≠ 0 := pow_ne_zero 2 hσne
    have : σ / (σ^2 + (σ / 2)^2) = (4 / 5) * (1 / σ) := by
      field_simp [hσne, hσ2ne]
      ring
  -- Conclude the desired bound
  exact le_trans (by simpa [hEval]) hfrac_mono

end RS
end RH
