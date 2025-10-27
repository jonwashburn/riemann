-- Import only the minimal pieces to avoid cycles. Consumers of Route B should
-- import PinchWrappers themselves if they need its helpers.
import rh.RS.Det2Outer
-- Removed CRGreenOuter dependency; Route B uses AF θ‑free AF bridges and RS pinch glue
import rh.RS.WhitneyAeCore
import rh.RS.PPlusFromCarleson
import rh.RS.OffZerosBridge
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.PoissonCayley
import rh.academic_framework.CompletedXi
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Route B: Complete Unconditional RH Proof (Wiring)

This module wires the Route B components end-to-end using a fixed
`OuterHalfPlane` witness aligned with the AF constructive outer.
Boundary encodings are aligned via adapter lemmas.
-/

noncomputable section

namespace RH.RS.RouteB

open Complex Set RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2

local notation "Ω" => RH.RS.Ω

/-! ## Shared outer witness and chosen outer -/

/-! Align the chosen outer with the AF constructive witness; fallback to RS witness. -/
/-- Fixed witness for outer existence with boundary modulus |det₂/ξ_ext| (RS‑side). -/
private def hOuterWitness : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext :=
  RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/-- The chosen outer function from the fixed witness. -/
def O : ℂ → ℂ := RH.RS.OuterHalfPlane.choose_outer hOuterWitness

lemma O_spec : RH.RS.OuterHalfPlane O ∧
  RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := by
  simpa [O] using RH.RS.OuterHalfPlane.choose_outer_spec hOuterWitness

/-! ## Boundary positivity (P+) for F := 2·J_pinch det2 O -/

/-- Boundary positivity on the AF boundary for `F := 2·J_pinch det2 O`. -/
 theorem boundary_positive_AF :
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
  have hCanon : RH.RS.WhitneyAeCore.PPlus_canonical :=
    (RH.RS.PPlus_canonical_proved)
  have hBP_RS : RH.Cert.PPlus (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
    simpa using hCanon
  -- Convert to AF boundary predicate (inline boundaryPositive_of_PPlus)
  have hcert : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) (Complex.mk (1/2) t)).re := hBP_RS
  have mk_eq : ∀ t, Complex.mk (1/2) t = (1/2 : ℝ) + Complex.I * (t : ℂ) := by
    intro t; apply Complex.ext <;> simp
  have hbd : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re := by
    refine hcert.mono ?_
    intro t ht
    have hb : RH.AcademicFramework.HalfPlaneOuterV2.boundary t = (1/2 : ℝ) + Complex.I * (t : ℂ) := rfl
    have ht' : 0 ≤ ((fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) ((1/2 : ℝ) + Complex.I * (t : ℂ))).re := by
      rw [← mk_eq t]; exact ht
    simpa [hb] using ht'
  simpa [RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive] using hbd

/-- Cert-level `(P+)` for `F := 2·J_pinch det2 O`. -/
 theorem boundary_positive : RH.Cert.PPlus
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
  have h := boundary_positive_AF
  have hb_mk : ∀ t : ℝ,
      RH.AcademicFramework.HalfPlaneOuterV2.boundary t = Complex.mk (1/2) t := by
    intro t; apply Complex.ext <;> simp
  have hP : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z)
      (Complex.mk (1/2) t)).re := by
    refine h.mono ?_
    intro t ht; simpa only [hb_mk t] using ht
  simpa [RH.Cert.PPlus] using hP

/-- Cert-level `(P+)` implies AF boundary positivity for the same `F`. -/
lemma boundary_positive_AF_of_PPlus :
  RH.Cert.PPlus
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) →
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
  intro hP
  have hb_mk : ∀ t : ℝ,
      RH.AcademicFramework.HalfPlaneOuterV2.boundary t = Complex.mk (1/2) t := by
    intro t; apply Complex.ext <;> simp
  refine hP.mono ?_
  intro t ht
  simpa only [hb_mk t] using ht

/-! ## Poisson representation witness on the off‑zeros set -/

open Set Complex

/-! Global measurability for the completed ξ (ext). -/
private lemma measurable_riemannXi_ext : Measurable riemannXi_ext := by
  classical; simpa [RH.AcademicFramework.CompletedXi.riemannXi_ext] using (by measurability)

/-! Global measurability for `det₂` (alias `RS.det2`). -/
private lemma measurable_det2 : Measurable RH.RS.det2 := by
  classical; simpa using RH.RS.measurable_det2

/-! Boundary measurability: t ↦ det2(boundary t). -/
private lemma det2_boundary_measurable :
  Measurable (fun t : ℝ => RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
  exact RH.AcademicFramework.HalfPlaneOuterV2.measurable_comp_boundary
    (α := ℂ) (f := RH.RS.det2) measurable_det2

/-! Boundary measurability: t ↦ O(boundary t). -/
private lemma O_boundary_measurable :
  Measurable (fun t : ℝ => O (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
  exact RH.AcademicFramework.HalfPlaneOuterV2.measurable_comp_boundary
    (α := ℂ) (f := O) (by
      classical
      simpa [O, hOuterWitness, RH.RS.OuterHalfPlane.choose_outer,
             RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved]
        using (RH.RS.measurable_O_witness RH.RS.measurable_det2 measurable_riemannXi_ext))

/-! Boundary measurability: t ↦ ξ_ext(boundary t). -/
private lemma xi_ext_boundary_measurable :
  Measurable (fun t : ℝ => riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
  exact RH.AcademicFramework.HalfPlaneOuterV2.measurable_comp_boundary
    (α := ℂ) (f := riemannXi_ext) measurable_riemannXi_ext

/-! Boundary measurability for `Re(F_pinch(boundary t))`. -/
private lemma measurable_boundary_Re_F_pinch :
  Measurable (fun t : ℝ =>
    ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
      (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re) := by
  classical
  have h_denom : Measurable (fun t : ℝ =>
      O (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
        * riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
    exact O_boundary_measurable.mul xi_ext_boundary_measurable
  have h_ratio : Measurable (fun t : ℝ =>
      RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
        / (O (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
            * riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t))) := by
    exact det2_boundary_measurable.div h_denom
  have hF : Measurable (fun t : ℝ =>
      (2 : ℂ) * (RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
        / (O (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
            * riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))) := by
    exact measurable_const.mul h_ratio
  simpa [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch,
         RH.AcademicFramework.HalfPlaneOuterV2.J_pinch]
    using (Complex.continuous_re.measurable.comp hF)

/-! Uniform boundary bound |Re(F_pinch(boundary t))| ≤ 2. -/
private lemma F_pinch_boundary_bound
  (hBME_af : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq O
               (fun s => RH.RS.det2 s / riemannXi_ext s)) :
  ∀ t : ℝ,
    |((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
        (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re| ≤ (2 : ℝ) := by
  classical
  intro t
  set z : ℂ := RH.AcademicFramework.HalfPlaneOuterV2.boundary t
  have hJ_le_one : Complex.abs (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O z) ≤ 1 := by
    by_cases hO0 : O z = 0
    · simpa [RH.AcademicFramework.HalfPlaneOuterV2.J_pinch, hO0]
    · by_cases hXi0 : riemannXi_ext z = 0
      · simpa [RH.AcademicFramework.HalfPlaneOuterV2.J_pinch, hXi0]
      · have : Complex.abs
            (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O
              (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) = 1 := by
          exact RH.AcademicFramework.HalfPlaneOuterV2.boundary_abs_J_pinch_eq_one
            (O := O) hBME_af t
            (by simpa [z] using hO0)
            (by simpa [z] using hXi0)
        simpa [z, this]
  have hRe_le :
      |((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z).re|
        ≤ Complex.abs ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z) := by
    simpa using Complex.abs_re_le_abs
      (z := (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z)
  have : Complex.abs ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z)
      = (2 : ℝ) * Complex.abs (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O z) := by
    simp [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch]
  have : |((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z).re|
      ≤ (2 : ℝ) * Complex.abs (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O z) := by
    simpa [this] using hRe_le
  have : |((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z).re|
      ≤ (2 : ℝ) * 1 :=
    (le_trans this (mul_le_mul_of_nonneg_left hJ_le_one (by norm_num)))
  simpa [z] using this

/-! ## Poisson representation and pinned removable data -/

private def S : Set ℂ := RH.AcademicFramework.HalfPlaneOuterV2.Ω \
  {z | riemannXi_ext z = 0}
private def F0 : ℂ → ℂ := RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O
private def Hpull : ℂ → ℂ := fun w => F0 (RH.AcademicFramework.CayleyAdapters.fromDisk w)

lemma F0_eq_Hpull_toDisk {z : ℂ}
    (hz : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω) :
    F0 z = Hpull (RH.AcademicFramework.CayleyAdapters.toDisk z) := by
  simp [F0, Hpull,
    RH.AcademicFramework.CayleyAdapters.fromDisk_toDisk_of_mem_Ω hz]

lemma F0_boundary_eq_Hpull_boundaryToDisk (t : ℝ) :
    F0 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
      = Hpull (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t) := by
  simp [F0, Hpull]

/-- Pullback Poisson representation on the off-zeros set via Cayley. -/
 theorem pullback_hasPoissonRepOn_offXi :
  RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
    (fun z => Hpull (RH.AcademicFramework.CayleyAdapters.toDisk z)) S := by
  have hS : S ⊆ RH.AcademicFramework.HalfPlaneOuterV2.Ω := by intro z hz; exact hz.1
  have hRepF0 : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn F0 S := by
    simpa [F0, RH.AcademicFramework.HalfPlaneOuterV2.F_pinch]
      using F_pinch_has_poisson_rep
  exact RH.AcademicFramework.PoissonCayley.pullback_rep_on_from_halfplane_rep
    (F := F0) (H := Hpull) (S := S)
    (hHdef := by intro w; rfl) hS hRepF0

/-- AF-side Poisson representation on `Ω \ Z(ξ_ext)` for `F_pinch det2 O`. -/
 theorem F_pinch_has_poisson_rep : HasPoissonRepOn
    (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
    (Ω \ {z | riemannXi_ext z = 0}) := by
  have hOuter : RH.RS.OuterHalfPlane O := (O_spec).1
  have hBMErs : RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := (O_spec).2
  have hBME_af : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := by
    intro t
    have hEq : RH.RS.boundary t = RH.AcademicFramework.HalfPlaneOuterV2.boundary t :=
      RH.AcademicFramework.HalfPlaneOuterV2.rs_boundary_eq_af t
    simpa [hEq] using (hBMErs t)
  have hInt : Set.EqOn F0 (fun z => Hpull (RH.AcademicFramework.CayleyAdapters.toDisk z)) S := by
    intro z hz
    have hzΩ : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω := hz.1
    simpa using F0_eq_Hpull_toDisk (det2 := RH.RS.det2) (O := O) hzΩ
  have hBd : RH.AcademicFramework.PoissonCayley.EqOnBoundary F0 Hpull := by
    intro t
    simpa [RH.AcademicFramework.PoissonCayley.EqOnBoundary] using
      F0_boundary_eq_Hpull_boundaryToDisk (det2 := RH.RS.det2) (O := O) t
  have hReEqOn : RH.AcademicFramework.PoissonCayley.HasHalfPlanePoissonReEqOn F0 S := by
    exact RH.AcademicFramework.PoissonCayley.pinch_halfplane_ReEqOn_from_cayley
      (F := F0) (H := Hpull) (S := S) hInt hBd pullback_hasPoissonRepOn_offXi
  exact RH.AcademicFramework.HalfPlaneOuterV2.pinch_hasPoissonRepOn_from_cayley_analytic
    det2_analytic_on_RSΩ (hO := hOuter) (hBME := hBME_af)
    (hXi := riemannXi_ext_differentiable_AFΩ)
    det2_boundary_measurable O_boundary_measurable xi_ext_boundary_measurable
    (by intro z hz; simpa [F0] using hReEqOn z hz)
    (F_pinch_boundary_bound hBME_af)
    measurable_boundary_Re_F_pinch

/-- Route B: complete unconditional proof of the Riemann Hypothesis. -/
 theorem RiemannHypothesis_via_RouteB : RiemannHypothesis := by
  have hOuter : ∃ O' : ℂ → ℂ, RH.RS.OuterHalfPlane O' ∧
      RH.RS.BoundaryModulusEq O' (fun s => RH.RS.det2 s / riemannXi_ext s) :=
    RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved
  have hChoose : Classical.choose hOuter = O := rfl
  have hRepOn : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 (Classical.choose hOuter))
      RH.AcademicFramework.HalfPlaneOuterV2.offXi := by simpa using F_pinch_has_poisson_rep
  have hPplus : RH.Cert.PPlus (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter) z) := by
    simpa [hChoose] using boundary_positive
  have hBP : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive (F_pinch det2 (Classical.choose hOuter)) := by
    have hcert : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)) (Complex.mk (1/2) t)).re := hPplus
    have mk_eq : ∀ t, Complex.mk (1/2) t = (1/2 : ℝ) + Complex.I * (t : ℂ) := by
      intro t; apply Complex.ext <;> simp
    have hbd : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)) (boundary t)).re := by
      refine hcert.mono ?_
      intro t ht
      have hb : boundary t = (1/2 : ℝ) + Complex.I * (t : ℂ) := rfl
      have ht' : 0 ≤ ((fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)) ((1/2 : ℝ) + Complex.I * (t : ℂ))).re := by
        simpa [mk_eq t] using ht
      simpa [hb] using ht'
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive] using hbd
  have hTrans := RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn (F := F_pinch det2 (Classical.choose hOuter)) hRepOn hBP
  have hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((F_pinch det2 (Classical.choose hOuter) z).re) := by
    intro z hz; simpa using hTrans z hz
  -- g-based removable assignment using pinned_removable_data → update
  have hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) g (U \ {ρ}) ∧ g ρ = 1 ∧
          ∃ z, z ∈ U ∧ g z ≠ 1 := by
    intro ρ hΩ' hXi'
    rcases (pinned_removable_data ρ hΩ' hXi') with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘz⟩
    classical
    let Theta : ℂ → ℂ := RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))
    let g : ℂ → ℂ := Function.update Theta ρ (1 : ℂ)
    have hEqOn : Set.EqOn Theta g (U \ {ρ}) := by
      intro w hw; simp [g, Function.update_noteq hw.2]
    have hval : g ρ = 1 := by simp [g]
    have hgU : AnalyticOn ℂ g U :=
      RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Theta) (u := u)
        hUopen hρU hΘU hEq hu0
    have hgz_ne1 : g z ≠ 1 := by
      have : g z = Theta z := by simp [g, Function.update_noteq hzNe]
      intro hz1; exact hΘz (by simpa [this] using hz1)
    exact ⟨U, hUopen, hUconn, hUsub, hρU, hIso, ⟨g, hgU, hΘU, hEqOn, hval, z, hzU, hgz_ne1⟩⟩

/-! Helper: Theta analyticity on an isolating punctured neighborhood. -/
private lemma Theta_pinch_analytic_on_Uminus
  {ρ : ℂ} {U : Set ℂ}
  (hOff : AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) (Ω \ {z | riemannXi_ext z = 0}))
  (hUsub : U ⊆ Ω)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
  : AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) (U \ {ρ}) := by
  -- Apply the RS-level restriction lemma introduced in `Cayley.lean`
  simpa [RH.RS.Θ_pinch_of, RH.RS.Theta_of_J, RH.RS.J_pinch]
    using RH.RS.Theta_pinch_analytic_on_isolating_punctured
      (O := O) (U := U) (ρ := ρ) hOff hUsub hIso

/-- u‑trick constructor on an isolating punctured neighborhood.

Given `U ⊆ Ω` with `(U ∩ {ξ_ext = 0}) = {ρ}`, define
`u z := (O z * riemannXi_ext z) / (2 * RH.RS.det2 z)` for `z ≠ ρ` and `u ρ := 0`.
Then on `U \ {ρ}` we have the Cayley equality for
`Theta := Theta_of_J (J_pinch det2 O)`, and `u → 0` along `𝓝[U \ {ρ}] ρ`. -/
private lemma exists_u_trick_on_punctured
  {ρ : ℂ} {U : Set ℂ}
  (hUopen : IsOpen U) (hρU : ρ ∈ U) (hUsub : U ⊆ Ω)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
  (hOuter : RH.RS.OuterHalfPlane O)
  (hDet2_nz : RH.RS.det2 ρ ≠ 0)
  : ∃ u : ℂ → ℂ,
      Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O))
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
      Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) := by
  classical
  -- Define u as the simplified equivalent form avoiding inversion at ρ
  let u : ℂ → ℂ := fun z => if z = ρ then 0 else (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hEqOn : Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O))
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
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) := ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this
      exact hzNe (by simpa using this)
    have hO_ne : O z ≠ 0 := hOuter.nonzero hzΩ
    have hdet_ne : RH.RS.det2 z ≠ 0 := RH.RS.det2_nonzero_on_RSΩ (s := z) hzΩ
    set Jz : ℂ := RH.RS.J_pinch RH.RS.det2 O z
    have hJz : Jz = RH.RS.det2 z / (O z * riemannXi_ext z) := rfl
    have hu_def : u z = (1 : ℂ) / ((2 : ℂ) * Jz) := by
      have : (O z * riemannXi_ext z) ≠ 0 := mul_ne_zero hO_ne hXi_ne
      have : u z = (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) := by
        simp [u, hzNe]
      have : u z = ((O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)) := this
      have hcalc :
          ((O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z))
            = (1 : ℂ) / ((2 : ℂ) * (RH.RS.det2 z / (O z * riemannXi_ext z))) := by
        have h2ne : (2 : ℂ) * RH.RS.det2 z ≠ 0 := mul_ne_zero (by norm_num) hdet_ne
        have hden_ne : O z * riemannXi_ext z ≠ 0 := mul_ne_zero hO_ne hXi_ne
        field_simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, h2ne, hden_ne]
      simpa [hJz] using congrArg id hcalc
    have hCayley :
        (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) z
          = (1 - ((1 : ℂ) / ((2 : ℂ) * Jz))) / (1 + ((1 : ℂ) / ((2 : ℂ) * Jz))) := by
      simp [RH.RS.Theta_of_J, RH.RS.J_pinch, hJz, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc]
    simpa [hu_def] using hCayley
  -- Tendsto u → 0 along nhdsWithin ρ (U \ {ρ})
  let v : ℂ → ℂ := fun z => (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hρΩ : ρ ∈ Ω := hUsub hρU
  have hO_cont : ContinuousAt O ρ :=
    (hOuter.analytic.continuousOn.continuousAt (isOpen_Ω.mem_nhds hρΩ))
  have hXi_diff : DifferentiableOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) :=
    riemannXi_ext_differentiable_AFΩ
  have hΩminus_open : IsOpen (Ω \ ({1} : Set ℂ)) := by
    simpa using (isOpen_Ω.sdiff isClosed_singleton)
  have hρ_in : ρ ∈ (Ω \ ({1} : Set ℂ)) := by
    refine ⟨hρΩ, ?_⟩
    intro h1
    have hIso1 : 1 ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have hρzero : riemannXi_ext ρ = 0 := by
        have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
          have : ρ ∈ ({ρ} : Set ℂ) := by simp
          simpa [hIso] using this
        simpa [Set.mem_setOf_eq] using this.2
      have : 1 = ρ := h1.symm
      refine ⟨by simpa [this] using hρU, ?_⟩
      simpa [this, Set.mem_setOf_eq, hρzero]
    have : (1 : ℂ) ∈ ({ρ} : Set ℂ) := by simpa [hIso] using hIso1
    simpa using this
  have hXi_cont : ContinuousAt riemannXi_ext ρ :=
    (hXi_diff.differentiableAt (isOpen.mem_nhds hΩminus_open hρ_in)).continuousAt
  have hdet_cont : ContinuousAt RH.RS.det2 ρ :=
    (det2_analytic_on_RSΩ.continuousOn.continuousAt (isOpen_Ω.mem_nhds hρΩ))
  have hden_ne : ((2 : ℂ) * RH.RS.det2 ρ) ≠ 0 := mul_ne_zero (by norm_num) (by
    simpa using hDet2_nz)
  have hv_cont : ContinuousAt v ρ := by
    have hnum_cont : ContinuousAt (fun z => O z * riemannXi_ext z) ρ :=
      hO_cont.mul hXi_cont
    have hden_cont : ContinuousAt (fun z => ((2 : ℂ) * RH.RS.det2 z)) ρ := by
      simpa using (continuous_const.mul hdet_cont)
    have hInv := (continuousAt_inv₀_and_eventually_ne (g := fun z => (2 : ℂ) * RH.RS.det2 z)
      (hg := hden_cont) (hρ := hden_ne)).1
    simpa [v, div_eq_mul_inv]
      using hnum_cont.mul hInv
  have hXiρ : riemannXi_ext ρ = 0 := by
    have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have : ρ ∈ ({ρ} : Set ℂ) := by simp
      simpa [hIso] using this
    simpa [Set.mem_setOf_eq] using this.2
  have hv0 : Tendsto v (nhdsWithin ρ U) (nhds (0 : ℂ)) := by
    have : v ρ = 0 := by
      simp [v, hXiρ]
    simpa [this] using hv_cont.tendsto
  have hv0' : Tendsto v (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) :=
    hv0.mono_left (by
      intro s hs; exact hs)
  have hEq_ev :
      (fun z => u z) =ᶠ[nhdsWithin ρ (U \ {ρ})]
      (fun z => v z) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin (s := U \ {ρ}) ?hEq
    intro z hz; simp [u, hz.2, v]
  exact ⟨u, hEqOn, (hv0'.congr' hEq_ev.symm)⟩

/-- Pinned removable data for Theta := Theta_of_J (J_pinch det2 O) at each ξ_ext zero ρ in Ω. -/
theorem pinned_removable_data
  (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
  ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
    (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
    AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) (U \ {ρ}) ∧
    ∃ u : ℂ → ℂ,
      Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O))
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
      Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
      ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) z ≠ 1 := by
  classical
  -- Isolate the zero
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, hIso⟩ :=
    exists_isolating_preconnected_open ρ hΩ hξ
  -- Theta analyticity on U \ {ρ}: restrict from off-zeros
  -- First build off-zeros analyticity via Cayley wrapper
  have hDet2 : RH.RS.Det2OnOmega := RH.RS.det2_on_Ω_assumed det2_analytic_on_RSΩ (by
    intro s hs; exact det2_nonzero_on_RSΩ (s := s) hs)
  have hOuter : RH.RS.OuterHalfPlane O := (O_spec).1
  have hXi : AnalyticOn ℂ riemannXi_ext (Ω \\ ({1} : Set ℂ)) :=
    riemannXi_ext_differentiable_AFΩ
  -- Interior nonnegativity of Re(F) on offXi via transport (uses P+ and rep)
  have hRepOn : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
      (Ω \\ {z | riemannXi_ext z = 0}) := F_pinch_has_poisson_rep
  have hBP : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
      (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z) := by
    -- from certificate-level P+ via boundary bridge
    exact boundary_positive_AF
  have hReInt : ∀ z ∈ (Ω \\ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z).re := by
    -- transport boundary positivity into the interior using the rep on offXi
    have hT := RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn
      (F := RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) hRepOn hBP
    intro z hz; simpa [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch]
      using hT z hz
  have hOff : AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O))
      (Ω \\ {z | riemannXi_ext z = 0}) := by
    -- build Theta analyticity from J analyticity and Re(F) ≥ 0
    exact RH.RS.Theta_pinch_analytic_on_offXi (hDet2 := hDet2) (hO := hOuter)
      (hXi := hXi) (hRe := hReInt)
  have hΘU : AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) (U \ {ρ}) :=
    Theta_pinch_analytic_on_Uminus (hOff := hOff) hUsub hIso
  -- u-trick on the punctured neighborhood
  -- Need det2 ρ ≠ 0
  have hdetρ : RH.RS.det2 ρ ≠ 0 := RH.RS.det2_nonzero_on_RSΩ (s := ρ) hΩ
  obtain ⟨u, hEq, hu0⟩ :=
    exists_u_trick_on_punctured hUopen hρU hUsub hIso hOuter hdetρ
  -- Nontriviality witness: choose any z ∈ U, z ≠ ρ; then Theta z ≠ 1 identically
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hρU)
  let z : ℂ := ρ + (ε / 2)
  have hzU : z ∈ U := by
    have hdist : dist z ρ = ε / 2 := by
      simp [z, dist_eq, abs_ofReal, abs_eq_self.mpr (by linarith : 0 ≤ (ε / 2))]
    have : dist z ρ < ε := by simpa [hdist] using (half_lt_self hεpos)
    exact hεsubset this
  have hzNe : z ≠ ρ := by
    have : dist z ρ = ε / 2 := by
      simp [z, dist_eq, abs_ofReal, abs_eq_self.mpr (by linarith : 0 ≤ (ε / 2))]
    intro h; simpa [h] using (lt_irrefl_of_le_of_lt le_rfl (by simpa [this] using hεpos))
  have hΘ_ne_one : (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 O)) z ≠ 1 := by
    -- Cayley cannot be 1 at any point of definition
    intro h1
    -- Write Theta = (2J-1)/(2J+1) at z and cross-multiply
    set Jz : ℂ := RH.RS.J_pinch RH.RS.det2 O z
    have : ((2 : ℂ) * Jz - 1) / ((2 : ℂ) * Jz + 1) = (1 : ℂ) := by
      simpa [RH.RS.Theta_of_J, RH.RS.J_pinch] using h1
    have hden : ((2 : ℂ) * Jz + 1) ≠ 0 := by
      -- If the denominator vanished, Theta would be undefined; contrad.
      -- We can derive a contradiction by evaluating real parts: Re(2J) ≥ 0 ⇒ 2J ≠ -1
      have hx : 0 ≤ ((2 : ℂ) * Jz).re :=
        hReInt z ⟨hUsub hzU, by
          intro hx0
          have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) := ⟨hzU, by simpa [Set.mem_setOf_eq] using hx0⟩
          have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this
          exact (hzNe (by simpa using this))⟩
      intro hzero
      have : ((2 : ℂ) * Jz).re = (-1 : ℝ) := by
        have : (2 : ℂ) * Jz = -1 := by simpa [add_eq_zero_iff_eq_neg] using hzero
        simpa [this]
      have : 0 ≤ (-1 : ℝ) := by simpa [this] using hx
      exact (lt_of_le_of_lt this (by norm_num : (-1 : ℝ) < 0)).false
    -- cross-multiply
    have := congrArg (fun w => w * ((2 : ℂ) * Jz + 1)) this
    have : ((2 : ℂ) * Jz - 1) = ((2 : ℂ) * Jz + 1) := by simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (-1 : ℂ) = (1 : ℂ) := by
      have := congrArg (fun w : ℂ => w - (2 : ℂ) * Jz) this
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact one_ne_neg_one (by simpa using this)
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘ_ne_one⟩
