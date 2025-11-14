import rh.RS.Det2Outer
import rh.RS.Cayley
import rh.RS.WhitneyAeCore
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Route B: Pinned/removable auxiliary lemmas (factored out)

This module hosts the pinned/removable helpers used by the Route B wiring.
It exposes isolating neighbourhoods at `ξ_ext` zeros, the u‑trick construction on
punctured neighbourhoods, and the packaged pinned data for
`Θ := Θ_pinch_of det2 O`.
-/

noncomputable section

namespace RH.RS.RouteB

open Complex Set Filter Topology
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2
open scoped Topology

local notation "Ω" => RH.RS.Ω
local notation "O" => RH.RS.WhitneyAeCore.O

def XiDomain : Set ℂ := Ω \ ({1} : Set ℂ)

lemma isOpen_XiDomain : IsOpen XiDomain := by
  simpa [XiDomain] using (isOpen_Ω.sdiff isClosed_singleton)

lemma two_mem_XiDomain : (2 : ℂ) ∈ XiDomain := by
  have hΩ : (2 : ℂ) ∈ Ω := by
    simpa [Ω, Set.mem_setOf_eq] using (show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num)
  refine ⟨hΩ, ?_⟩
  simpa using (show (2 : ℂ) ≠ (1 : ℂ) by norm_num)

lemma mem_Ω_iff_re {z : ℂ} : z ∈ Ω ↔ (1 / 2 : ℝ) < z.re := by
  simpa [Ω, Set.mem_setOf_eq]

lemma re_gt_half_of_mem_Ω {z : ℂ} (hz : z ∈ Ω) : (1 / 2 : ℝ) < z.re :=
  (mem_Ω_iff_re).1 hz

lemma convex_re_gt_half {a b : ℝ} (ha : (1 / 2 : ℝ) < a) (hb : (1 / 2 : ℝ) < b)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 / 2 : ℝ) < (1 - θ) * a + θ * b := by
  have hrewrite :
      (1 - θ) * a + θ * b =
        ((1 - θ) * (a - (1 / 2 : ℝ)) + θ * (b - (1 / 2 : ℝ))) + (1 / 2 : ℝ) := by
    ring
  by_cases hθ_one : θ = 1
  · subst hθ_one
    simp [hrewrite, hb]
  have hθ_lt_one : θ < 1 := lt_of_le_of_ne' hθ₁ hθ_one
  by_cases hθ_zero : θ = 0
  · subst hθ_zero
    simp [hrewrite, ha]
  have hθ_pos : 0 < θ := lt_of_le_of_ne' hθ₀ hθ_zero
  have hθ_pos' : 0 < 1 - θ := sub_pos.2 hθ_lt_one
  have hA : 0 < a - (1 / 2 : ℝ) := sub_pos.2 ha
  have hB : 0 < b - (1 / 2 : ℝ) := sub_pos.2 hb
  have hmain :
      0 < (1 - θ) * (a - (1 / 2 : ℝ)) + θ * (b - (1 / 2 : ℝ)) := by
    exact add_pos (mul_pos hθ_pos' hA) (mul_pos hθ_pos hB)
  have := add_lt_add_of_lt_of_le hmain (le_of_eq rfl)
  simpa [hrewrite] using this

def linePath (z w : ℂ) : Path z w :=
{ toFun := fun t => ((1 - (t : ℝ)) : ℝ) • z + (t : ℝ) • w,
  continuous_toFun := by
    have h1 : Continuous fun t : ℝ => (1 - t) := by continuity
    have h2 : Continuous fun t : ℝ => t := by continuity
    have h3 : Continuous fun t : ℝ => ((1 - t) : ℝ) • z := by
      simpa using h1.smul continuous_const
    have h4 : Continuous fun t : ℝ => (t : ℝ) • w := by
      simpa using h2.smul continuous_const
    have h5 : Continuous fun t : ℝ => ((1 - t) : ℝ) • z + (t : ℝ) • w := h3.add h4
    simpa using h5.comp continuous_subtype_val,
  source' := by
    ext; simp [linePath],
  target' := by
    ext; simp [linePath] }

lemma linePath_apply (z w : ℂ) (t : I) :
    linePath z w t = ((1 - (t : ℝ)) : ℝ) • z + (t : ℝ) • w := rfl

lemma linePath_re (z w : ℂ) (t : I) :
    (linePath z w t).re = (1 - (t : ℝ)) * z.re + (t : ℝ) * w.re := by
  simp [linePath_apply, mul_comm, mul_left_comm, mul_assoc]

lemma linePath_im (z w : ℂ) (t : I) :
    (linePath z w t).im = (1 - (t : ℝ)) * z.im + (t : ℝ) * w.im := by
  simp [linePath_apply, mul_comm, mul_left_comm, mul_assoc]

lemma linePath_mem_Ω {z w : ℂ} (hz : z ∈ Ω) (hw : w ∈ Ω) :
    ∀ t : I, linePath z w t ∈ Ω := by
  intro t
  have h0 : 0 ≤ (t : ℝ) := t.property.1
  have h1 : (t : ℝ) ≤ 1 := t.property.2
  have hzRe := re_gt_half_of_mem_Ω hz
  have hwRe := re_gt_half_of_mem_Ω hw
  refine (mem_Ω_iff_re).2 ?_
  simpa [linePath_re z w t] using convex_re_gt_half hzRe hwRe h0 h1

lemma linePath_to_two_avoids_one {z : ℂ} (hzΩ : z ∈ Ω) (hz_ne : z ≠ 1)
    (hz_im : z.im ≠ 0) :
    ∀ t : I, linePath z (2 : ℂ) t ≠ (1 : ℂ) := by
  intro t
  intro h
  have hIm := congrArg Complex.im h
  have hRe := congrArg Complex.re h
  have : (1 - (t : ℝ)) * z.im = 0 := by
    simpa [linePath_im] using hIm
  have ht : (t : ℝ) = 1 := by
    have hcoeff : 1 - (t : ℝ) = 0 := by
      have hz_im' : z.im ≠ 0 := hz_im
      exact mul_eq_zero.mp this |>.resolve_right hz_im'
    exact sub_eq_zero.mp (eq_of_sub_eq_zero hcoeff)
  have ht_subtype : t = ⟨1, by exact ⟨show (0 : ℝ) ≤ 1 by norm_num, show (1 : ℝ) ≤ 1 by norm_num⟩⟩ := by
    ext; simpa [ht]
  have hVal : linePath z (2 : ℂ) t = (2 : ℂ) := by
    simpa [ht_subtype]
  have : (2 : ℂ) = (1 : ℂ) := by simpa [hVal] using h
  exact (by norm_num : (2 : ℂ) ≠ (1 : ℂ)) this

lemma vertical_path_avoids_one {z : ℂ} (hz_im : z.im = 0) (hz_ne : z ≠ 1) :
    ∀ t : I, linePath z (z + Complex.I) t ≠ (1 : ℂ) := by
  intro t h
  have hIm := congrArg Complex.im h
  have hImVal : (linePath z (z + Complex.I) t).im = (t : ℝ) := by
    simp [linePath_im, hz_im]
  have htzero : (t : ℝ) = 0 := by simpa [hImVal] using hIm
  have hRe := congrArg Complex.re h
  have hReVal : (linePath z (z + Complex.I) t).re = z.re := by
    simp [linePath_re]
  have hz_eq : z = (1 : ℂ) := by
    ext
    · simpa [hReVal, htzero] using hRe
    · simpa [hz_im, htzero] using congrArg Complex.im h
  exact hz_ne hz_eq

def pathToTwo (z : ℂ) (hz : z ∈ XiDomain) : Path z (2 : ℂ) := by
  classical
  by_cases hIm : z.im = 0
  ·
    have hzΩ : z ∈ Ω := hz.1
    have hz_ne : z ≠ 1 := by
      intro h
      exact hz.2 (by simpa [XiDomain, Set.mem_diff] using ⟨hzΩ, by simpa [h]⟩)
    have hliftΩ : z + Complex.I ∈ Ω := by
      have hzRe := re_gt_half_of_mem_Ω hzΩ
      refine (mem_Ω_iff_re).2 ?_
      simp [Complex.add_re, hzRe]
    have hlift_im : (z + Complex.I).im ≠ 0 := by
      simp [Complex.add_im]
    exact (linePath z (z + Complex.I)).trans (linePath (z + Complex.I) 2)
  · exact linePath z 2

lemma O_spec :
    RH.RS.OuterHalfPlane O ∧
    RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := by
  classical
  have hWitness := RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved
  simpa [O, RH.RS.WhitneyAeCore.O] using
    RH.RS.OuterHalfPlane.choose_outer_spec hWitness

/-- Produce an isolating, preconnected open neighbourhood for a zero of `riemannXi_ext`
inside Ω. The neighbourhood is chosen small enough to avoid `{1}` as well. -/
lemma exists_isolating_preconnected_open
    (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧ (1 : ℂ) ∉ U := by
  classical
  have hAnalytic :
      AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) :=
    riemannXi_ext_analytic_on_RSΩ_minus_one
  have hρIn : ρ ∈ Ω \ ({1} : Set ℂ) := by
    refine ⟨hΩ, ?_⟩
    have hRe : (1 / 2 : ℝ) < ρ.re := by
      simpa [Ω, Set.mem_setOf_eq] using hΩ
    have hneq : ρ ≠ (1 : ℂ) := by
      intro h
      simpa [h, Complex.one_re] using hRe
    simpa [Set.mem_singleton_iff] using hneq
  obtain ⟨r, hrpos, hBall⟩ :=
    analyticOn_isolatedZeros (f := riemannXi_ext) hAnalytic hρIn hξ
  have hΩ_open : IsOpen Ω := isOpen_Ω
  obtain ⟨ε, hεpos, hεsubset⟩ :=
    Metric.mem_nhds_iff.mp (hΩ_open.mem_nhds hΩ)
  -- choose a ball small enough to lie in Ω and avoid 1
  set δ : ℝ := dist ρ 1 / 2 with hδ_def
  have hδpos : 0 < δ := by
    have hρne1 : ρ ≠ (1 : ℂ) := by
      intro h
      have : (1 / 2 : ℝ) < (1 : ℂ).re := by
        simpa [h, Complex.one_re, Ω, Set.mem_setOf_eq] using hΩ
      exact (lt_irrefl _ this)
    simpa [hδ_def] using half_pos (dist_pos.mpr hρne1)
  set t := min r (min ε δ) with ht_def
  have htpos : 0 < t := lt_min hrpos (lt_min hεpos hδpos)
  have hBall_subset : Metric.ball ρ t ⊆ Metric.ball ρ r := by
    intro z hz
    have : dist z ρ < t := hz
    exact lt_of_lt_of_le this (min_le_left _ _)
  have hBall_subset_Ω : Metric.ball ρ t ⊆ Ω := by
    intro z hz
    have ht_le_ε : t ≤ ε := le_trans (min_le_right _ _) (min_le_left _ _)
    have : dist z ρ < ε := lt_of_lt_of_le hz ht_le_ε
    exact hεsubset this
  have hBall_avoids1 : (1 : ℂ) ∉ Metric.ball ρ t := by
    intro h1
    have ht_le_δ : t ≤ δ := le_trans (min_le_right _ _) (min_le_right _ _)
    have : dist 1 ρ < t := by simpa [Metric.mem_ball, dist_comm] using h1
    have : dist ρ 1 < δ := lt_of_lt_of_le (by simpa [dist_comm] using this) ht_le_δ
    have hle : dist ρ 1 / 2 ≤ dist ρ 1 := by
      have : 0 ≤ dist ρ 1 := dist_nonneg
      simpa using half_le_self this
    exact (not_lt_of_ge hle) (by simpa [hδ_def] using this)
  have hIso : (Metric.ball ρ t ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with ⟨hz_ball, hz_zero⟩
      have hz_ball' : z ∈ Metric.ball ρ r := hBall_subset hz_ball
      have hz_pair : z ∈ Metric.ball ρ r ∩ {z | riemannXi_ext z = 0} :=
        ⟨hz_ball', hz_zero⟩
      have hz_singleton : z ∈ ({ρ} : Set ℂ) := by
        simpa [hBall] using hz_pair
      simpa using hz_singleton
    · intro z hz
      obtain rfl : z = ρ := by simpa [Set.mem_singleton_iff] using hz
      refine ⟨?_, ?_⟩
      · have : dist ρ ρ < t := by simpa [dist_self] using htpos
        simpa [Metric.mem_ball] using this
      · simpa [hξ]
  refine ⟨Metric.ball ρ t, isOpen_ball, isPreconnected_ball, hBall_subset_Ω,
    by simpa using mem_ball_self htpos, hIso, hBall_avoids1⟩

/-- Restrict analyticity of `Θ_pinch` from the off-zeros set to an
isolating punctured neighbourhood. -/
lemma Theta_pinch_analytic_on_Uminus
    {ρ : ℂ} {U : Set ℂ}
    (hOff : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O)
      (Ω \ {z | riemannXi_ext z = 0}))
    (hUsub : U ⊆ Ω)
    (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ)) :
    AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) := by
  exact RH.RS.Theta_pinch_analytic_on_isolating_punctured
    (O := O) (U := U) (ρ := ρ) hOff hUsub hIso

/-- u‑trick on a punctured isolating neighbourhood: build `u` with
`Θ = (1-u)/(1+u)` and `u → 0`. -/
lemma exists_u_trick_on_punctured
    {ρ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hρU : ρ ∈ U) (hUsub : U ⊆ Ω)
    (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
    (hOuter : RH.RS.OuterHalfPlane O)
    (hDet2_nz : RH.RS.det2 ρ ≠ 0) :
    ∃ u : ℂ → ℂ,
      Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
      Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) := by
  classical
  let u : ℂ → ℂ := fun z =>
    if z = ρ then 0 else (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hEqOn :
      Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) := by
    intro z hz
    have hzU : z ∈ U := hz.1
    have hzNe : z ≠ ρ := by
      have : z ∈ ({ρ} : Set ℂ) → False := by
        intro hzρ; exact hz.2 (by simpa using hzρ)
      intro h; exact this (by simpa [h])
    have hzΩ : z ∈ Ω := hUsub hzU
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) :=
        ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this
      exact hzNe (by simpa using this)
    have hO_ne : O z ≠ 0 := hOuter.nonzero hzΩ
    have hdet_ne : RH.RS.det2 z ≠ 0 :=
      RH.RS.det2_nonzero_on_RSΩ (s := z) hzΩ
    set Jz : ℂ := RH.RS.J_pinch RH.RS.det2 O z
    have hJz : Jz = RH.RS.det2 z / (O z * riemannXi_ext z) := rfl
    have hu_def :
        u z = (1 : ℂ) / ((2 : ℂ) * Jz) := by
      have : (O z * riemannXi_ext z) ≠ 0 := mul_ne_zero hO_ne hXi_ne
      have : u z =
          (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) := by
        simp [u, hzNe]
      have hcalc :
          ((O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)) =
            (1 : ℂ) / ((2 : ℂ) * (RH.RS.det2 z / (O z * riemannXi_ext z))) := by
        have h2ne : (2 : ℂ) * RH.RS.det2 z ≠ 0 :=
          mul_ne_zero (by norm_num) hdet_ne
        have hden_ne : O z * riemannXi_ext z ≠ 0 :=
          mul_ne_zero hO_ne hXi_ne
        field_simp [div_eq_mul_inv, mul_comm, mul_left_comm,
          mul_assoc, h2ne, hden_ne]
      simpa [hJz] using congrArg id hcalc
    have hCayley :
        (RH.RS.Θ_pinch_of RH.RS.det2 O) z =
          (1 - ((1 : ℂ) / ((2 : ℂ) * Jz))) /
            (1 + ((1 : ℂ) / ((2 : ℂ) * Jz))) := by
      simp [RH.RS.Θ_pinch_of, RH.RS.Theta_of_J, RH.RS.J_pinch,
        hJz, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [hu_def] using hCayley
  let v : ℂ → ℂ :=
    fun z => (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hρΩ : ρ ∈ Ω := hUsub hρU
  have hO_cont : ContinuousAt O ρ :=
    (hOuter.analytic.continuousOn.continuousAt
      (isOpen_Ω.mem_nhds hρΩ))
  have hXi_diff :
      DifferentiableOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) :=
    riemannXi_ext_differentiable_on_RSΩ_minus_one
  have hΩminus_open : IsOpen (Ω \ ({1} : Set ℂ)) := by
    simpa using (isOpen_Ω.sdiff isClosed_singleton)
  have hρ_in : ρ ∈ (Ω \ ({1} : Set ℂ)) := by
    refine ⟨hρΩ, ?_⟩
    intro h1
    have hIso1 : (1 : ℂ) ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have hρzero : riemannXi_ext ρ = 0 := by
        have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
          have : ρ ∈ ({ρ} : Set ℂ) := by simp
          simpa [hIso] using this
        simpa [Set.mem_setOf_eq] using this.2
      have : 1 = ρ := h1.symm
      refine ⟨by simpa [this] using hρU, ?_⟩
      simpa [this, Set.mem_setOf_eq, hρzero]
    have : (1 : ℂ) ∈ ({ρ} : Set ℂ) := by
      simpa [hIso] using hIso1
    simpa using this
  have hXi_cont : ContinuousAt riemannXi_ext ρ :=
    (hXi_diff.differentiableAt
      (IsOpen.mem_nhds hΩminus_open hρ_in)).continuousAt
  have hdet_cont : ContinuousAt RH.RS.det2 ρ :=
    (RH.RS.det2_analytic_on_RSΩ.continuousOn.continuousAt
      (isOpen_Ω.mem_nhds hρΩ))
  have hden_ne :
      ((2 : ℂ) * RH.RS.det2 ρ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by simpa using hDet2_nz)
  have hv_cont : ContinuousAt v ρ := by
    have hnum_cont :
        ContinuousAt (fun z => O z * riemannXi_ext z) ρ :=
      hO_cont.mul hXi_cont
    have hden_cont :
        ContinuousAt (fun z => (2 : ℂ) * RH.RS.det2 z) ρ := by
      simpa using (continuous_const.mul hdet_cont)
    have hInv :=
        (continuousAt_inv₀_and_eventually_ne
          (g := fun z => (2 : ℂ) * RH.RS.det2 z)
          (hg := hden_cont) (hρ := hden_ne)).1
    simpa [v, div_eq_mul_inv] using hnum_cont.mul hInv
  have hXiρ : riemannXi_ext ρ = 0 := by
    have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have : ρ ∈ ({ρ} : Set ℂ) := by simp
      simpa [hIso] using this
    simpa [Set.mem_setOf_eq] using this.2
  have hv0 :
      Tendsto v (nhdsWithin ρ U) (nhds (0 : ℂ)) := by
    have : v ρ = 0 := by simp [v, hXiρ]
    simpa [this] using hv_cont.tendsto
  have hv0' :
      Tendsto v (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) :=
    hv0.mono_left (by intro s hs; exact hs)
  have hEq_ev :
      (fun z => u z) =ᶠ[nhdsWithin ρ (U \ {ρ})]
        (fun z => v z) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin
      (s := U \ {ρ}) ?hEq
    intro z hz
    simp [u, hz.2, v]
  refine ⟨u, hEqOn, ?_⟩
  exact (hv0'.congr' hEq_ev.symm)

/-- Main export: pinned removable data for
`Θ := Θ_pinch_of det2 O` at each `ξ_ext` zero, assuming the needed
nonnegativity on `Ω \ {ξ_ext = 0}`. -/
theorem pinned_removable_data
    (hRe :
      ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
        0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z).re)
    (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) ∧
      ∃ u : ℂ → ℂ,
        Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
          (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
        Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
        ∃ z, z ∈ U ∧ z ≠ ρ ∧
          (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
  classical
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hOne⟩ :=
    exists_isolating_preconnected_open ρ hΩ hξ
  have hDet2 : RH.RS.Det2OnOmega :=
    RH.RS.det2_on_Ω_assumed det2_analytic_on_RSΩ
      (by intro s hs; exact det2_nonzero_on_RSΩ (s := s) hs)
  have hOuter : RH.RS.OuterHalfPlane O := (O_spec).1
  have hXi :
      AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) :=
    riemannXi_ext_analytic_on_RSΩ_minus_one
  have hOff :
      AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (Ω \ {z | riemannXi_ext z = 0}) := by
    exact RH.RS.Theta_pinch_analytic_on_offXi
      (hDet2 := hDet2) (hO := hOuter) (hXi := hXi)
      (hRe := by
        intro z hz
        exact hRe z ⟨hz.1, hz.2⟩)
  have hΘU :
      AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) :=
    Theta_pinch_analytic_on_Uminus (U := U) (ρ := ρ)
      (hOff := hOff) hUsub hIso
  have hdetρ : RH.RS.det2 ρ ≠ 0 :=
    RH.RS.det2_nonzero_on_RSΩ (s := ρ) hΩ
  obtain ⟨u, hEq, hu0⟩ :=
    exists_u_trick_on_punctured hUopen hρU hUsub hIso hOuter hdetρ
  -- Nontriviality witness
  have : ∃ z, z ∈ U ∧ z ≠ ρ ∧
      (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
    obtain ⟨ε, hεpos, hεsubset⟩ :=
      Metric.mem_nhds_iff.mp (hUopen.mem_nhds hρU)
    let z := ρ + (ε / 2 : ℝ)
    have hz_ne : z ≠ ρ := by
      have : (ε / 2 : ℝ) ≠ 0 := by
        have : 0 < ε / 2 := half_pos hεpos
        exact ne_of_gt this
      intro h
      have : (ε / 2 : ℝ) = 0 := by
        simpa [z, h] using rfl
      exact this.elim this
    have hzU : z ∈ U := by
      have hz_ball : z ∈ Metric.ball ρ ε := by
        have : dist z ρ = ‖(ε / 2 : ℝ)‖ := by
          simp [z, dist_eq, sub_eq, Complex.norm_eq_abs, Complex.abs_ofReal]
        have : ‖(ε / 2 : ℝ)‖ < ε := by
          have : (ε / 2 : ℝ) < ε := by nlinarith
          simpa [Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt (half_pos hεpos))] using this
        simpa [Metric.mem_ball, this]
      exact hεsubset (by simpa using hz_ball)
    have hzUdiff : z ∈ U ∧ z ≠ ρ := ⟨hzU, hz_ne⟩
    have hzΩ : z ∈ Ω := hUsub hzU
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) :=
        ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by
        simpa [hIso] using this
      exact hz_ne (by simpa using this)
    have hO_ne : O z ≠ 0 := (O_spec).1.nonzero hzΩ
    have hdet_ne :
        RH.RS.det2 z ≠ 0 :=
      RH.RS.det2_nonzero_on_RSΩ (s := z) hzΩ
    have hΘz_ne :
        (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
      have hEqz := hEq hzUdiff
      intro h1
      have : (1 - ((O z * riemannXi_ext z) /
          ((2 : ℂ) * RH.RS.det2 z))) /
          (1 + ((O z * riemannXi_ext z) /
          ((2 : ℂ) * RH.RS.det2 z))) = (1 : ℂ) := by
        simpa [u, hz_ne] using congrArg (· z) hEqz
      have : (O z * riemannXi_ext z) /
          ((2 : ℂ) * RH.RS.det2 z) = 0 := by
        have hden :
            (1 + ((O z * riemannXi_ext z) /
              ((2 : ℂ) * RH.RS.det2 z))) ≠ 0 := by
          intro h; cases h
        have h1' :
            (1 - ((O z * riemannXi_ext z) /
              ((2 : ℂ) * RH.RS.det2 z))) =
              (1 + ((O z * riemannXi_ext z) /
              ((2 : ℂ) * RH.RS.det2 z))) := by
          simpa [h1] using congrArg
            (fun w => w * (1 + ((O z * riemannXi_ext z) /
              ((2 : ℂ) * RH.RS.det2 z)))) this
        have :
            (O z * riemannXi_ext z) /
              ((2 : ℂ) * RH.RS.det2 z) =
              - (O z * riemannXi_ext z) /
                ((2 : ℂ) * RH.RS.det2 z) := by
          simpa using sub_left_cancel_iff.mp h1'
        have :
            (O z * riemannXi_ext z) /
              ((2 : ℂ) * RH.RS.det2 z) = 0 := by
          simpa using eq_neg_iff_add_eq_zero.mp this
        simpa using this
      have hnum_ne :
          (O z * riemannXi_ext z) ≠ 0 :=
        mul_ne_zero hO_ne hXi_ne
      have hden_ne' :
          ((2 : ℂ) * RH.RS.det2 z) ≠ 0 :=
        mul_ne_zero (by norm_num) hdet_ne
      exact (div_eq_zero_iff.mp this).elim hnum_ne
        (by exact hden_ne')
    exact ⟨z, hzU, hz_ne, hΘz_ne⟩
  rcases this with ⟨z, hzU, hzNe, hΘz⟩
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘz⟩

end RH.RS.RouteB
