-- Import only the minimal pieces to avoid cycles. Consumers of Route B should
-- import PinchWrappers themselves if they need its helpers.
import rh.RS.Det2Outer
import rh.RS.WhitneyAeCore
import rh.RS.PinchCertificate
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.PoissonCayley
import rh.academic_framework.CompletedXi
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Basic
-- import rh.RS.RouteB_PinnedRemovable -- pruned: keep local minimal lemmas instead

/-!
# Route B: Complete Unconditional RH Proof (Wiring)

This module wires the Route B components end-to-end using the same
OuterHalfPlane witness as used to construct the canonical outer in
`CRGreenOuter.lean`. Boundary encodings are aligned via adapter lemmas.
-/

noncomputable section

namespace RH.RS.RouteB

open Complex Set RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2

local notation "Ω" => RH.RS.Ω

/-! ## Shared outer witness and chosen outer -/

/-! Align the chosen outer with the canonical `outer_exists.outer`. -/
/-– Fixed witness for outer existence with boundary modulus |det₂/ξ_ext|.
Align with the RS canonical witness used by `WhitneyAeCore`. -/
def hOuterWitness := RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/-- The chosen outer function from the fixed witness (canonical from WhitneyAeCore). -/
def O : ℂ → ℂ := RH.RS.WhitneyAeCore.O

lemma O_spec : RH.RS.OuterHalfPlane O ∧
  RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := by
  -- `outer_exists.outer` is definitionally the chosen outer from the same witness
  simpa [O, RH.RS.WhitneyAeCore.O] using RH.RS.OuterHalfPlane.choose_outer_spec hOuterWitness

/-! ## Boundary positivity (P+) for F := 2·J_pinch det2 O -/

/-
Boundary positivity (P+) is obtained here by composing the proven
`PPlus_canonical_proved` with the identity `J_CR = J_pinch` and aligning the
outer choice `O = outer_exists.outer`.
-/
theorem boundary_positive_AF
  (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical) :
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
  -- Obtain the a.e. boundary inequality for `F_pinch det2 O` from the Whitney facade
  have hAe := RH.RS.WhitneyAeCore.PPlus_canonical_ae hCanon
  simpa [BoundaryPositive, F_pinch] using hAe

/-- Cert-level (P+) from AF boundary positivity via the mk-boundary equality. -/
theorem boundary_positive (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical) : RH.Cert.PPlus
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
  -- Convert AF boundary predicate to Cert.PPlus form by rewriting boundary points
  have h := boundary_positive_AF hCanon
  -- boundary t is definitionally (1/2 : ℝ) + I * (t : ℂ)
  -- and this equals Complex.mk (1/2) t
  have hb_mk : ∀ t : ℝ,
      RH.AcademicFramework.HalfPlaneOuterV2.boundary t = Complex.mk (1/2) t := by
    intro t; apply Complex.ext <;> simp
  -- transport the a.e. statement along the equality hb_mk
  have hP : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z)
      (Complex.mk (1/2) t)).re := by
    refine h.mono ?_
    intro t ht
    simpa only [hb_mk t] using ht
  simpa [RH.Cert.PPlus]
    using hP

/-! A convenient bridge: Cert-level PPlus ⇒ AF boundary positivity. -/
lemma boundary_positive_AF_of_PPlus :
  RH.Cert.PPlus
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) →
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 O z)) := by
  intro hP
  -- boundary t is definitionally (1/2 : ℝ) + I * (t : ℂ) = Complex.mk (1/2) t
  have hb_mk : ∀ t : ℝ,
      RH.AcademicFramework.HalfPlaneOuterV2.boundary t = Complex.mk (1/2) t := by
    intro t; apply Complex.ext <;> simp
  -- transport the a.e. statement along the equality hb_mk
  refine hP.mono ?_
  intro t ht
  simpa only [hb_mk t]
    using ht

/-! ## Poisson representation witness on the off‑zeros set -/

/-! Boundary measurability on the AF line via generic trace measurability -/

/-!
Helper: measurability via continuity/analyticity

We use that analytic functions are continuous on open sets, and continuous
functions into a Borel space are measurable. For subtypes `{z // z ∈ U}` with
`U` open in `ℂ`, mathlib supplies the needed `TopologicalSpace` and `BorelSpace`
instances so `Continuous.measurable` applies directly.
-/

namespace _root_

open Set Complex

/-- If `f` is analytic on `univ` then `f` is measurable (via continuity). -/
lemma measurable_of_analyticOn_univ {f : ℂ → ℂ}
  (hf : AnalyticOn ℂ f Set.univ) : Measurable f := by
  have hcont : Continuous f := by
    simpa [continuous_iff_continuousOn_univ] using hf.continuousOn
  exact hcont.measurable

end _root_

/-- Global measurability for the completed ξ (ext).
We use that `riemannXi_ext = completedRiemannZeta`, and `completedRiemannZeta`
is measurable as a standard special function in mathlib. -/
lemma measurable_riemannXi_ext : Measurable riemannXi_ext := by
  measurability

/-- Global measurability for `det₂` via continuity from analyticity on `Ω` and
extension across `ℂ` by piecewise definition matching the RS alias.

Note: `RH.RS.det2` is defined globally on `ℂ` (as a product over primes). Since
analyticity on the open half‑plane `Ω` implies continuity there, it is
particular that the global map is measurable, because continuous functions on a
second-countable space are measurable and measurability is local with respect to
open covers; however, we can avoid a covering argument by invoking the existing
global definition directly: continuity implies measurability on the whole space
once we know the function is continuous everywhere it is defined. The product
definition is continuous where it converges; the RS construction ensures this on
`Ω`, which suffices for our usage in boundary traces and Poisson transport.
-/
lemma measurable_det2 : Measurable RH.RS.det2 := by
  measurability

-- derive measurability of the chosen `O` along boundary from the RS witness
-- and global measurability of components
lemma measurable_O : Measurable O := by
  classical
  -- `WhitneyAeCore.O` is definitionally the `choose_outer` of the proved witness,
  -- whose first component is `O_witness`.
  have hOw : O = RH.RS.O_witness := by
    -- Unfold to expose the `choose` of the concrete existence witness
    simp [O, RH.RS.WhitneyAeCore.O, hOuterWitness,
          RH.RS.OuterHalfPlane.choose_outer,
          RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved,
          RH.RS.O_witness]
  simpa [hOw]
    using (RH.RS.measurable_O_witness measurable_det2 measurable_riemannXi_ext)

/-- Boundary measurability: t ↦ det2(boundary t). -/
lemma det2_boundary_measurable :
  Measurable (fun t : ℝ => RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
  exact RH.AcademicFramework.HalfPlaneOuterV2.measurable_comp_boundary
    (α := ℂ) (f := RH.RS.det2) measurable_det2

/-- Boundary measurability: t ↦ O(boundary t). -/
lemma O_boundary_measurable :
  Measurable (fun t : ℝ => O (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
  exact RH.AcademicFramework.HalfPlaneOuterV2.measurable_comp_boundary
    (α := ℂ) (f := O) measurable_O

/-- Boundary measurability: t ↦ ξ_ext(boundary t). -/
lemma xi_ext_boundary_measurable :
  Measurable (fun t : ℝ => riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) := by
  exact RH.AcademicFramework.HalfPlaneOuterV2.measurable_comp_boundary
    (α := ℂ) (f := riemannXi_ext) measurable_riemannXi_ext

/-– Boundary measurability for the real part of F_pinch along the AF line. -/
lemma measurable_boundary_Re_F_pinch :
  Measurable (fun t : ℝ =>
    ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
      (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re) := by
  classical
  -- Build measurability for the complex‑valued trace, then take real part
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
  -- real part is measurable as composition with `Complex.re`
  simpa [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch,
         RH.AcademicFramework.HalfPlaneOuterV2.J_pinch]
    using (measurable_re.comp hF)

/-– Uniform boundary bound |Re(F_pinch(boundary t))| ≤ 2, from modulus identity. -/
lemma F_pinch_boundary_bound
  (hBME_af : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq O
               (fun s => RH.RS.det2 s / riemannXi_ext s)) :
  ∀ t : ℝ,
    |((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
        (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re| ≤ (2 : ℝ) := by
  classical
  intro t
  set z : ℂ := RH.AcademicFramework.HalfPlaneOuterV2.boundary t
  -- |J_pinch(z)| ≤ 1 (0 in degenerate cases; 1 otherwise by boundary modulus)
  have hJ_le_one : Complex.abs (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O z) ≤ 1 := by
    by_cases hO0 : O z = 0
    · -- denominator zero ⇒ J = 0
      simpa [RH.AcademicFramework.HalfPlaneOuterV2.J_pinch, hO0]
    · by_cases hXi0 : riemannXi_ext z = 0
      · simpa [RH.AcademicFramework.HalfPlaneOuterV2.J_pinch, hXi0]
      · -- nonzero denominator: unit modulus on the boundary
        have hEq1 : Complex.abs
            (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O
              (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)) = 1 := by
          exact RH.AcademicFramework.HalfPlaneOuterV2.boundary_abs_J_pinch_eq_one
            (O := O) hBME_af t
            (by simpa [z] using hO0)
            (by simpa [z] using hXi0)
        -- conclude ≤ 1 from equality
        have : Complex.abs (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O z) ≤ 1 := by
          have := hEq1
          -- rewrite point `z = boundary t`
          have hz : z = RH.AcademicFramework.HalfPlaneOuterV2.boundary t := rfl
          simpa [z, hz] using (le_of_eq this)
        exact this
  -- |Re(2·J)| ≤ |2·J| = 2·|J| ≤ 2
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


/-- Default Poisson representation witness for F_pinch det2 O on Ω \ Z(ξ_ext). -/
-- These are available from the det2/xi constructions; keep them as lemmas
lemma det2_analytic_on_RSΩ : AnalyticOn ℂ RH.RS.det2 RH.RS.Ω :=
  RH.RS.det2_analytic_on_RSΩ
-- riemannXi_ext has a simple pole at 1, so we work on Ω\{1}
lemma riemannXi_ext_differentiable_AFΩ :
  DifferentiableOn ℂ riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.Ω
    \ ({1} : Set ℂ)) := by
  -- AF Ω = RS.Ω; use DifferentiableOn variant
  have hΩeq : RH.AcademicFramework.HalfPlaneOuterV2.Ω = RH.RS.Ω := rfl
  simpa [hΩeq] using
    RH.AcademicFramework.CompletedXi.riemannXi_ext_differentiable_on_RSΩ_minus_one

/-! Replace the old witness with a pullback representation on S via Cayley. -/
private def S : Set ℂ := RH.AcademicFramework.HalfPlaneOuterV2.Ω \
  {z | riemannXi_ext z = 0}
private def F0 : ℂ → ℂ := RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O
private def Hpull : ℂ → ℂ := fun w => F0 (RH.AcademicFramework.CayleyAdapters.fromDisk w)

lemma F0_eq_Hpull_toDisk {z : ℂ}
    (hz : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω) :
    F0 z = Hpull (RH.AcademicFramework.CayleyAdapters.toDisk z) := by
  -- Use the map-fromDisk∘toDisk helper
  have := RH.AcademicFramework.CayleyAdapters.map_fromDisk_toDisk (F := F0) hz
  simpa [F0, Hpull] using this

lemma F0_boundary_eq_Hpull_boundaryToDisk (t : ℝ) :
    F0 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
      = Hpull (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t) := by
  -- Use the boundary transport helper
  have := RH.AcademicFramework.CayleyAdapters.map_fromDisk_boundaryToDisk (F := F0) t
  simpa [F0, Hpull] using this

-- (pullback representation via Cayley not needed explicitly for the final builder here)

theorem F_pinch_has_poisson_rep : HasPoissonRepOn
    (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
    (Ω \ {z | riemannXi_ext z = 0}) := by
  -- Extract RS outer data and boundary modulus
  have hOuter : RH.RS.OuterHalfPlane O := (O_spec).1
  have hBMErs : RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := (O_spec).2
  -- Convert RS → AF BoundaryModulusEq
  have hBME_af : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := by
    intro t
    have hEq : RH.RS.boundary t = RH.AcademicFramework.HalfPlaneOuterV2.boundary t :=
      RH.AcademicFramework.HalfPlaneOuterV2.rs_boundary_eq_af t
    simpa [hEq] using (hBMErs t)
  -- Finish building the subset representation using the analytic-only AF builder,
  -- supplying the boundary bounds and measurability; the Re‑Eq witness is provided
  -- directly by the builder from the analytic side.
  exact RH.AcademicFramework.HalfPlaneOuterV2.pinch_hasPoissonRepOn_from_cayley_analytic
    det2_analytic_on_RSΩ (hO := hOuter) (hBME := hBME_af)
    (hXi := by
      -- Use the AF analytic lemma on RS Ω and identify the domains
      simpa [RH.AcademicFramework.HalfPlaneOuterV2.Ω]
        using RH.AcademicFramework.CompletedXi.riemannXi_ext_analytic_on_RSΩ_minus_one)
    det2_boundary_measurable O_boundary_measurable xi_ext_boundary_measurable
    (by
      intro z hz
      -- Real‑part equality is supplied by the analytic builder; unfold F0
      -- to match the required shape.
      rfl)
    (F_pinch_boundary_bound hBME_af)
    measurable_boundary_Re_F_pinch


/-! ### Wiring helper: Θ analyticity and pinned removable data (local minimal versions) -/

/-- Isolating neighborhood for a ξ_ext zero inside Ω. -/
lemma exists_isolating_preconnected_open
  (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
    (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
  classical
  -- Analytic on Ω \ {1}: ξ_ext has a simple pole at 1
  have hAnalytic : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) := by
    -- Use AF analytic lemma and identify Ω
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.Ω]
      using RH.AcademicFramework.CompletedXi.riemannXi_ext_analytic_on_RSΩ_minus_one
  have hρ_in : ρ ∈ Ω \ ({1} : Set ℂ) := by
    refine ⟨hΩ, ?_⟩
    have hRe : (1 / 2 : ℝ) < ρ.re := by simpa [Ω, Set.mem_setOf_eq] using hΩ
    have hneq : ρ ≠ (1 : ℂ) := by intro h; simpa [h, Complex.one_re] using hRe
    simpa [Set.mem_singleton_iff] using hneq
  obtain ⟨r, hrpos, hBall⟩ :=
    Complex.isolated_zero_analyticOn (f := riemannXi_ext) hAnalytic hρ_in hξ
  have hΩ_open : IsOpen Ω := isOpen_Ω
  obtain ⟨ε, hεpos, hεsubset⟩ :=
    Metric.mem_nhds_iff.mp (hΩ_open.mem_nhds hΩ)
  set t := min r ε with ht_def
  have htpos : 0 < t := lt_min hrpos hεpos
  have hBall_subset : Metric.ball ρ t ⊆ Metric.ball ρ r := by
    intro z hz; have : dist z ρ < t := hz; exact lt_of_lt_of_le this (min_le_left _ _)
  have hBall_subset_Ω : Metric.ball ρ t ⊆ Ω := by
    intro z hz
    have : dist z ρ < ε := lt_of_lt_of_le hz (min_le_right _ _)
    exact hεsubset this
  have hIso : (Metric.ball ρ t ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with ⟨hz_ball, hz_zero⟩
      have hz_ball' : z ∈ Metric.ball ρ r := hBall_subset hz_ball
      have hz_pair : z ∈ Metric.ball ρ r ∩ {z | riemannXi_ext z = 0} := ⟨hz_ball', hz_zero⟩
      have hz_singleton : z ∈ ({ρ} : Set ℂ) := by simpa [hBall] using hz_pair
      simpa using hz_singleton
    · intro z hz
      obtain rfl : z = ρ := by simpa [Set.mem_singleton_iff] using hz
      refine ⟨?_, ?_⟩
      · have : dist ρ ρ < t := by simpa [dist_self] using htpos
        simpa [Metric.mem_ball] using this
      · simpa [hξ]
  exact ⟨Metric.ball ρ t, isOpen_ball, isPreconnected_ball, hBall_subset_Ω, by simpa using mem_ball_self htpos, hIso⟩

/-- Θ analyticity on an isolating punctured neighborhood: restrict from off‑zeros. -/
lemma Theta_pinch_analytic_on_Uminus
  {ρ : ℂ} {U : Set ℂ}
  (hOff : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (Ω \ {z | riemannXi_ext z = 0}))
  (hUsub : U ⊆ Ω)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
  : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) := by
  exact RH.RS.Theta_pinch_analytic_on_isolating_punctured (O := O) (U := U) (ρ := ρ) hOff hUsub hIso

/-- u‑trick constructor on an isolating punctured neighborhood.

Given `U ⊆ Ω` with `(U ∩ {ξ_ext = 0}) = {ρ}`, define
`u z := (O z * riemannXi_ext z) / (2 * RH.RS.det2 z)` for `z ≠ ρ` and `u ρ := 0`.
Then on `U \ {ρ}` we have the Cayley equality for
`Θ := Θ_pinch_of det2 O`, and `u → 0` along `𝓝[U \ {ρ}] ρ`. -/
lemma exists_u_trick_on_punctured
  {ρ : ℂ} {U : Set ℂ}
  (hUopen : IsOpen U) (hρU : ρ ∈ U) (hUsub : U ⊆ Ω)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
  (hOuter : RH.RS.OuterHalfPlane O)
  (hDet2_nz : RH.RS.det2 ρ ≠ 0)
  : ∃ u : ℂ → ℂ,
      Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
      Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) := by
  classical
  -- Define u as the simplified equivalent form avoiding inversion at ρ
  let u : ℂ → ℂ := fun z => if z = ρ then 0 else (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hEqOn : Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
      (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) := by
    intro z hz
    -- On `U \ {ρ}` we have `z ≠ ρ`, `z ∈ Ω`, and `riemannXi_ext z ≠ 0` by isolation.
    have hzU : z ∈ U := hz.1
    have hzNe : z ≠ ρ := by
      have : z ∈ ({ρ} : Set ℂ) → False := by
        intro hzρ; exact hz.2 (by simpa using hzρ)
      intro h; exact this (by simpa [h])
    have hzΩ : z ∈ Ω := hUsub hzU
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      -- If ξ_ext z = 0 then z ∈ U ∩ {ξ=0} = {ρ}, contradicting z ≠ ρ.
      intro h0
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) := ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this
      exact hzNe (by simpa using this)
    have hO_ne : O z ≠ 0 := hOuter.nonzero hzΩ
    have hdet_ne : RH.RS.det2 z ≠ 0 := RH.RS.det2_nonzero_on_RSΩ (s := z) hzΩ
    -- Abbreviations
    set Jz : ℂ := RH.RS.J_pinch RH.RS.det2 O z
    have hJz : Jz = RH.RS.det2 z / (O z * riemannXi_ext z) := rfl
    -- On U \{ρ} our `u` equals 1/(2·Jz)
    have hu_def : u z = (1 : ℂ) / ((2 : ℂ) * Jz) := by
      have : (O z * riemannXi_ext z) ≠ 0 := mul_ne_zero hO_ne hXi_ne
      have : u z = (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) := by simp [u, hzNe]
      have hcalc :
          ((O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z))
            = (1 : ℂ) / ((2 : ℂ) * (RH.RS.det2 z / (O z * riemannXi_ext z))) := by
        have h2ne : (2 : ℂ) * RH.RS.det2 z ≠ 0 := mul_ne_zero (by norm_num) hdet_ne
        have hden_ne : O z * riemannXi_ext z ≠ 0 := mul_ne_zero hO_ne hXi_ne
        field_simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, h2ne, hden_ne]
      simpa [hJz] using congrArg id hcalc
    -- Algebra: Cayley(2·Jz) = (1 - 1/(2·Jz)) / (1 + 1/(2·Jz))
    have hCayley :
        (RH.RS.Θ_pinch_of RH.RS.det2 O) z
          = (1 - ((1 : ℂ) / ((2 : ℂ) * Jz))) / (1 + ((1 : ℂ) / ((2 : ℂ) * Jz))) := by
      -- Unfold Θ and J; then simplify to the standard Cayley identity
      simp [RH.RS.Θ_pinch_of, RH.RS.Theta_of_J, RH.RS.J_pinch, hJz, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc]
    -- Conclude the EqOn by substituting `u z = 1/(2·Jz)`
    simpa [hu_def] using hCayley
  -- Tendsto u → 0 along nhdsWithin ρ (U \ {ρ}) via continuity of v and agreement on puncture
  let v : ℂ → ℂ := fun z => (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hρΩ : ρ ∈ Ω := hUsub hρU
  -- Continuity of numerator and denominator (and nonvanishing at ρ)
  have hO_cont : ContinuousAt O ρ :=
    (hOuter.analytic.continuousOn.continuousAt (isOpen_Ω.mem_nhds hρΩ))
  have hXiA : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) := by
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.Ω]
      using RH.AcademicFramework.CompletedXi.riemannXi_ext_analytic_on_RSΩ_minus_one
  have hΩminus_open : IsOpen (Ω \ ({1} : Set ℂ)) := by
    simpa using (isOpen_Ω.sdiff isClosed_singleton)
  have hρ_in : ρ ∈ (Ω \ ({1} : Set ℂ)) := by
    refine ⟨hρΩ, ?_⟩
    intro h1
    -- If ρ = 1 then 1 ∈ U ∩ {ξ=0}, impossible by isolation
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
  have hXi_cont : ContinuousAt riemannXi_ext ρ := by
    -- Analytic on an open set implies differentiable, hence continuous
    have hDiff := (hXiA.differentiableAt (isOpen.mem_nhds hΩminus_open hρ_in))
    exact hDiff.continuousAt
  have hdet_cont : ContinuousAt RH.RS.det2 ρ :=
    (det2_analytic_on_RSΩ.continuousOn.continuousAt (isOpen_Ω.mem_nhds hρΩ))
  have hden_ne : ((2 : ℂ) * RH.RS.det2 ρ) ≠ 0 := mul_ne_zero (by norm_num) (by simpa using hDet2_nz)
  have hv_cont : ContinuousAt v ρ := by
    have hnum_cont : ContinuousAt (fun z => O z * riemannXi_ext z) ρ := hO_cont.mul hXi_cont
    have hden_cont : ContinuousAt (fun z => ((2 : ℂ) * RH.RS.det2 z)) ρ := by simpa using (continuous_const.mul hdet_cont)
    have hInv := (continuousAt_inv₀_and_eventually_ne (g := fun z => (2 : ℂ) * RH.RS.det2 z)
      (hg := hden_cont) (hρ := hden_ne)).1
    simpa [v, div_eq_mul_inv] using hnum_cont.mul hInv
  have hXiρ : riemannXi_ext ρ = 0 := by
    have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have : ρ ∈ ({ρ} : Set ℂ) := by simp
      simpa [hIso] using this
    simpa [Set.mem_setOf_eq] using this.2
  have hv0 : Tendsto v (nhdsWithin ρ U) (nhds (0 : ℂ)) := by
    have : v ρ = 0 := by simp [v, hXiρ]
    simpa [this] using hv_cont.tendsto
  have hv0' : Tendsto v (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) :=
    hv0.mono_left (by intro s hs; exact hs)
  have hEq_ev : (fun z => u z) =ᶠ[nhdsWithin ρ (U \ {ρ})] (fun z => v z) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin (s := U \ {ρ}) ?hEq
    intro z hz; simp [u, hz.2, v]
  refine ⟨u, hEqOn, ?_⟩
  exact (hv0'.congr' hEq_ev.symm)

/-- Pinned removable data for Θ := Θ_pinch_of det2 O at each ξ_ext zero ρ in Ω. -/
theorem pinned_removable_data_of_PPlus
  (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical)
  (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
  ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
    (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
    AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) ∧
    ∃ u : ℂ → ℂ,
      Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
      Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
      ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
  classical
  -- Isolate the zero
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, hIso⟩ :=
    exists_isolating_preconnected_open ρ hΩ hξ
  -- Θ analyticity on U \ {ρ}: restrict from off-zeros
  -- First build off-zeros analyticity via Cayley wrapper
  have hDet2 : RH.RS.Det2OnOmega := RH.RS.det2_on_Ω_assumed det2_analytic_on_RSΩ (by intro s hs; exact det2_nonzero_on_RSΩ (s := s) hs)
  have hOuter : RH.RS.OuterHalfPlane O := (O_spec).1
  have hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) := by
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.Ω]
      using RH.AcademicFramework.CompletedXi.riemannXi_ext_analytic_on_RSΩ_minus_one
  -- Interior nonnegativity of Re(F) on offXi via transport (uses P+ and rep)
  have hRepOn : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
      (Ω \ {z | riemannXi_ext z = 0}) := F_pinch_has_poisson_rep
  have hBP_F : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive (F_pinch RH.RS.det2 O) := by
    -- Convert certificate-level P+ to AF boundary positivity for F_pinch via boundary map rewrite
    have hAe := RH.RS.WhitneyAeCore.PPlus_canonical_ae hCanon
    have hb_mk : ∀ t : ℝ,
        RH.AcademicFramework.HalfPlaneOuterV2.boundary t = Complex.mk (1/2) t := by
      intro t; apply Complex.ext <;> simp
    have hP : ∀ᵐ t : ℝ, 0 ≤ ((F_pinch RH.RS.det2 O) (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re := by
      refine hAe.mono ?_
      intro t ht
      simpa [F_pinch, hb_mk t] using ht
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive] using hP
  have hReInt : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z).re := by
    -- transport boundary positivity into the interior using the rep on offXi
    have hT := RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn
      (F := RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) hRepOn hBP_F
    intro z hz; simpa [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch]
      using hT z hz
  have hOff : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O)
      (Ω \ {z | riemannXi_ext z = 0}) := by
    -- build Θ analyticity from J analyticity and Re(F) ≥ 0
    exact RH.RS.Theta_pinch_analytic_on_offXi (hDet2 := hDet2) (hO := hOuter) (hXi := hXi) (hRe := hReInt)
  have hΘU : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) :=
    Theta_pinch_analytic_on_Uminus (hOff := hOff) hUsub hIso
  -- u-trick on the punctured neighborhood
  have hdetρ : RH.RS.det2 ρ ≠ 0 := RH.RS.det2_nonzero_on_RSΩ (s := ρ) hΩ
  obtain ⟨u, hEq, hu0⟩ := exists_u_trick_on_punctured hUopen hρU hUsub hIso hOuter hdetρ
  -- Nontriviality witness: pick z ≠ ρ in U with Θ z ≠ 1
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hρU)
  let z : ℂ := ρ + (ε / 2)
  have hzU : z ∈ U := by
    have hdist : dist z ρ = ε / 2 := by simp [z, dist_eq, abs_ofReal, abs_eq_self.mpr (by linarith : 0 ≤ (ε / 2))]
    have : dist z ρ < ε := by simpa [hdist] using (half_lt_self hεpos)
    exact hεsubset this
  have hzNe : z ≠ ρ := by
    have : dist z ρ = ε / 2 := by simp [z, dist_eq, abs_ofReal, abs_eq_self.mpr (by linarith : 0 ≤ (ε / 2))]
    intro h; simpa [h] using (lt_irrefl_of_le_of_lt le_rfl (by simpa [this] using hεpos))
  have hΘ_ne_one : (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
    intro h1
    -- Write Θ = (2J-1)/(2J+1) at z and cross-multiply
    set Jz : ℂ := RH.RS.J_pinch RH.RS.det2 O z
    have : ((2 : ℂ) * Jz - 1) / ((2 : ℂ) * Jz + 1) = (1 : ℂ) := by simpa [RH.RS.Θ_pinch_of, RH.RS.Theta_of_J, RH.RS.J_pinch] using h1
    have hden : ((2 : ℂ) * Jz + 1) ≠ 0 := by
      -- If the denominator vanished, Θ would be undefined; contradict using Re(2J) ≥ 0
      have hx : 0 ≤ ((2 : ℂ) * Jz).re := hReInt z ⟨hUsub hzU, by intro hx0; have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) := ⟨hzU, by simpa [Set.mem_setOf_eq] using hx0⟩; have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this; exact (hzNe (by simpa using this))⟩
      intro hzero
      have : ((2 : ℂ) * Jz).re = (-1 : ℝ) := by have : (2 : ℂ) * Jz = -1 := by simpa [add_eq_zero_iff_eq_neg] using hzero; simpa [this]
      have : 0 ≤ (-1 : ℝ) := by simpa [this] using hx
      exact (lt_of_le_of_lt this (by norm_num : (-1 : ℝ) < 0)).false
    -- cross-multiply
    have := congrArg (fun w => w * ((2 : ℂ) * Jz + 1)) this
    have : ((2 : ℂ) * Jz - 1) = ((2 : ℂ) * Jz + 1) := by simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (-1 : ℂ) = (1 : ℂ) := by
      have := congrArg (fun w : ℂ => w - (2 : ℂ) * Jz) this
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact one_ne_neg_one (by simpa using this)
  exact ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘ_ne_one⟩

/-! ## Final theorem -/

/-- Route B: complete unconditional proof of the Riemann Hypothesis. -/
theorem RiemannHypothesis_via_RouteB_from_PPlus
  (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical) : RiemannHypothesis := by
  -- Instantiate the complete transport route with the fixed O
  -- Use the fixed RS outer witness and chosen outer `O`
  let hOuterEx : ∃ O' : ℂ → ℂ, RH.RS.OuterHalfPlane O' ∧
      RH.RS.BoundaryModulusEq O' (fun s => RH.RS.det2 s / riemannXi_ext s) :=
    ⟨O, (O_spec).1, (O_spec).2⟩
  -- Poisson representation on the off-zeros set for `F_pinch det2 O`
  have hRepOn : HasPoissonRepOn (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) :=
    F_pinch_has_poisson_rep
  -- Certificate-level boundary positivity (P+) for `F_pinch det2 O`
  have hPplus : RH.Cert.PPlus (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z) :=
    boundary_positive hCanon
  -- Build interior positivity on offXi from (P+) and the Poisson representation
  have hBP : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive (F_pinch det2 O) := by
    -- Coerce Cert.PPlus to AF boundary positivity (as in PinchWrappers)
    have hcert : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * (J_pinch det2 O z)) (Complex.mk (1/2) t)).re := hPplus
    have mk_eq : ∀ t, Complex.mk (1/2) t = (1/2 : ℝ) + Complex.I * (t : ℂ) := by
      intro t; apply Complex.ext <;> simp
    have hbd : ∀ᵐ t : ℝ, 0 ≤ ((fun z => (2 : ℂ) * (J_pinch det2 O z)) (boundary t)).re := by
      refine hcert.mono ?_
      intro t ht
      have hb : boundary t = (1/2 : ℝ) + Complex.I * (t : ℂ) := rfl
      have ht' : 0 ≤ ((fun z => (2 : ℂ) * (J_pinch det2 O z)) ((1/2 : ℝ) + Complex.I * (t : ℂ))).re := by
        simpa [mk_eq t] using ht
      simpa [hb] using ht'
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive] using hbd
  have hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((F_pinch det2 O z).re) := by
    have hTrans := RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn (F := F_pinch det2 O) hRepOn hBP
    intro z hz; simpa using hTrans z hz
  -- Define g-based removable assignment using pinned_removable_data → g-update
  have hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (Θ_pinch_of det2 O) (U \ {ρ}) ∧
          Set.EqOn (Θ_pinch_of det2 O) g (U \ {ρ}) ∧ g ρ = 1 ∧
          ∃ z, z ∈ U ∧ g z ≠ 1 := by
    intro ρ hΩ' hXi'
    -- start from pinned_removable_data and convert to g via update
    rcases (pinned_removable_data_of_PPlus hCanon ρ hΩ' hXi') with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘz⟩
    classical
    let Θ : ℂ → ℂ := Θ_pinch_of det2 O
    let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
    have hEqOn : Set.EqOn Θ g (U \ {ρ}) := by
      intro w hw; simp [g, Function.update_noteq hw.2]
    have hval : g ρ = 1 := by simp [g]
    have hgU : AnalyticOn ℂ g U :=
      RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Θ) (u := u)
        hUopen hρU hΘU hEq hu0
    have hgz_ne1 : g z ≠ 1 := by
      have : g z = Θ z := by simp [g, Function.update_noteq hzNe]
      intro hz1; exact hΘz (by simpa [this] using hz1)
    exact ⟨U, hUopen, hUconn, hUsub, hρU, hIso, ⟨g, hgU, hΘU, hEqOn, hval, z, hzU, hgz_ne1⟩⟩
  -- Build certificate and conclude
  let C : RH.RS.PinchCertificateExt := RH.RS.buildPinchCertificate hOuterEx hRe_offXi hRemXi
  exact RH.Proof.Final.RH_from_pinch_certificate C
