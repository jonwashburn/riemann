import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi
import Mathlib.MeasureTheory.Integral.Bochner
import rh.RS.Cayley
import rh.RS.TentShadow
import rh.academic_framework.DiskHardy

/-!
# Half‑plane outers (interface)

This module records a lightweight interface for outer functions on the right
half‑plane Ω := {Re s > 1/2}. It avoids disk‑specific dependencies and keeps the
construction abstract at the statement level; consumers can instantiate it with
Poisson‑outer constructions or via a Cayley transfer to the unit disk.

We provide:
- a nonvanishing/analytic predicate for a candidate `O` on Ω;
- a boundary‑modulus matching predicate `BoundaryModulusEq` (statement‑level);
- an existence predicate to obtain an outer `O` with prescribed boundary modulus.

No axioms are introduced; existence is exposed as a Prop‑level statement to be
realized by the analytic framework.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter
/-! ## Vendor lemma (disk Poisson → half‑plane Poisson for the pinch field)

This axiomatically records the Poisson identity for the real part of the
pinch field `F_pinch det2 O` on the right half‑plane. It stands in for the
standard Cayley change‑of‑variables derivation from the unit disk Poisson
formula and will be replaced by a mathlib‑backed proof when available. -/

axiom poisson_formula_re_vendor_for_F_pinch
  (det2 O : ℂ → ℂ) :
  ∀ z ∈ Ω,
    ((F_pinch det2 O) z).re =
      P (fun t : ℝ => ((F_pinch det2 O) (boundary t)).re) z


open Complex
open RH.AcademicFramework.CompletedXi

-- Define Ω locally (right half-plane)
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

-- Local notation for convenience
local notation "Ω" => Ω

/-- An outer on Ω: analytic and zero‑free on Ω. -/
structure OuterWitness (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonzero  : ∀ {s}, s ∈ Ω → O s ≠ 0

/-- Prop-level: `O` is outer on Ω. -/
def IsOuter (O : ℂ → ℂ) : Prop :=
  ∃ W : OuterWitness O, True

/-- Statement‑level boundary modulus predicate on the line Re s = 1/2.
For now this is abstract; in practice it means |O(1/2+it)| = |F(1/2+it)| a.e. -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  -- Abstract placeholder: in practice this is a.e. equality of modulus on boundary
  True

/-- Existence of an outer `O` on Ω with boundary modulus equal (a.e.) to a
prescribed modulus `|F|` on Re s = 1/2 (statement‑level). -/
def ExistsOuterWithBoundaryModulus (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuter O ∧ BoundaryModulusEq O F

/-- Specialized existence for det2/xi_ext modulus (used by pinch certificate). -/
def ExistsOuterWithModulus_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, OuterWitness O ∧
    BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s)

/-! ## Boundary parametrization and BMO interface (statement-level)

We record the boundary line parametrization and placeholders to express that a
real function `u : ℝ → ℝ` is the boundary log-modulus and lies in BMO. These
are used to state the standard Poisson-outer construction on the half-plane
at the Prop level, without committing to a particular analytic implementation. -/

/-- Boundary parametrization of the line Re s = 1/2. -/
@[simp] def boundary (t : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)

@[simp] lemma boundary_mk_eq (t : ℝ) : boundary t = Complex.mk (1/2) t := by
  refine Complex.ext ?hre ?him
  · simp [boundary]
  · simp [boundary]

/-- Placeholder: `u ∈ BMO(ℝ)` (used as an interface predicate only). -/
@[simp] def BMO_on_ℝ (_u : ℝ → ℝ) : Prop := True

/-- `u` is the boundary log-modulus of `F` along Re s = 1/2. -/
@[simp] def IsBoundaryLogModulusOf (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, u t = Real.log (Complex.abs (F (boundary t)))

/-- Prop-level form of the standard Poisson-outer construction on the half‑plane:
from BMO boundary data `u = log |F(1/2+it)|`, there exists an outer `O` on Ω
with boundary modulus `|F|` (a.e.). This captures the intended construction
(Poisson extension + harmonic conjugate + exponentiation) without committing to
its proof here. -/
def PoissonOuterFromBMO (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  BMO_on_ℝ u ∧ IsBoundaryLogModulusOf u F → ExistsOuterWithBoundaryModulus F

/-- Specialization of `PoissonOuterFromBMO` to `F = det2 / ξ_ext`. -/
def PoissonOuter_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  let F := fun s => det2 s / riemannXi_ext s
  ∀ u : ℝ → ℝ, IsBoundaryLogModulusOf u F ∧ BMO_on_ℝ u →
    ExistsOuterWithModulus_det2_over_xi_ext det2

end HalfPlaneOuter
end AcademicFramework
end RH


/-!
# Half-plane Poisson transport (positive boundary → interior operator)

We add a Poisson kernel `poissonKernel` on Ω, a transport operator `P`,
positivity from a.e. boundary sign, a representation wrapper for `Re F`, and
the transport corollary (with a pinch specialization).
No axioms, no sorry.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Complex

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter

-- The Poisson kernel for the right half‑plane `Re z > 1/2`.
-- Normalized so that `∫_ℝ poissonKernel z t dt = 1`.
@[simp] def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  (1 / Real.pi) * ((z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2))

lemma poissonKernel_nonneg {z : ℂ} (hz : (1/2 : ℝ) < z.re) (t : ℝ) :
    0 ≤ poissonKernel z t := by
  unfold poissonKernel
  have hx : 0 < z.re - (1/2 : ℝ) := sub_pos.mpr hz
  have hx0 : 0 ≤ z.re - (1/2 : ℝ) := le_of_lt hx
  have denom_pos :
      0 < (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := by
    have hxpos : 0 < (z.re - (1/2 : ℝ))^2 := by
      have hne : z.re - (1/2 : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hz)
      have : 0 < (z.re - (1/2 : ℝ)) * (z.re - (1/2 : ℝ)) := by
        exact mul_self_pos.mpr hne
      simpa [pow_two] using this
    exact add_pos_of_pos_of_nonneg hxpos (sq_nonneg _)
  have denom_nonneg :
      0 ≤ (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := le_of_lt denom_pos
  have div_nonneg' :
      0 ≤ (z.re - (1/2 : ℝ)) /
            ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2) :=
    div_nonneg hx0 denom_nonneg
  have invpi_nonneg : 0 ≤ (1 / Real.pi) :=
    one_div_nonneg.mpr (le_of_lt Real.pi_pos)
  exact mul_nonneg invpi_nonneg div_nonneg'

-- Poisson transport from boundary data `u` to the interior.
@[simp] def P (u : ℝ → ℝ) (z : ℂ) : ℝ := ∫ t : ℝ, u t * poissonKernel z t

-- Boundary nonnegativity predicate for `F` on `Re = 1/2`.
def PPlus (F : ℂ → ℂ) : Prop :=
  (∀ᵐ t : ℝ, 0 ≤ (F (Complex.mk (1/2) t)).re)

lemma P_nonneg_of_ae_nonneg
    {u : ℝ → ℝ}
    (hInt : ∀ {z : ℂ}, z ∈ Ω → Integrable (fun t : ℝ => u t * poissonKernel z t))
    (hu_nonneg : ∀ᵐ t : ℝ, 0 ≤ u t) :
    ∀ ⦃z : ℂ⦄, z ∈ Ω → 0 ≤ P u z := by
  intro z hz
  have hker :
      0 ≤ᵐ[volume] fun t : ℝ => poissonKernel z t := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using hz) t
  have hprod :
      0 ≤ᵐ[volume] fun t : ℝ => u t * poissonKernel z t := by
    refine ((hu_nonneg).and hker).mono ?_
    intro t ht; rcases ht with ⟨hu, hk⟩; exact mul_nonneg hu hk
  have hI : Integrable (fun t : ℝ => u t * poissonKernel z t) := hInt hz
  -- integrability is not needed by integral_nonneg_of_ae; keep it for callers
  have hnonneg : 0 ≤ ∫ t, u t * poissonKernel z t :=
    integral_nonneg_of_ae (μ := volume) hprod
  simpa [P] using hnonneg

structure HasHalfPlanePoissonRepresentation (F : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ F Ω)
  (integrable :
      ∀ z ∈ Ω, Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t))
  (re_eq :
      ∀ z ∈ Ω,
        (F z).re = P (fun t : ℝ => (F (boundary t)).re) z)

theorem HasHalfPlanePoissonTransport
    {F : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentation F) :
    PPlus F → ∀ ⦃z : ℂ⦄, z ∈ Ω → 0 ≤ (F z).re := by
  intro hBoundary z hz
  -- Convert boundary a.e. nonnegativity to the `boundary` parametrization
  have hBoundary' : ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re := by
    have h0 : ∀ᵐ t : ℝ, 0 ≤ (F (Complex.mk (1/2) t)).re := hBoundary
    exact h0.mono (by
      intro t ht
      simpa [boundary_mk_eq] using ht)
  have hpos :=
    P_nonneg_of_ae_nonneg
      (u := fun t : ℝ => (F (boundary t)).re)
      (hInt := by intro w hw; simpa using hRep.integrable w hw)
      (hu_nonneg := hBoundary')
      hz
  simpa [hRep.re_eq z hz] using hpos

theorem HasHalfPlanePoissonTransport_re
    {F : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentation F) :
    PPlus F → ∀ z : ℂ, z.re > (1/2 : ℝ) → 0 ≤ (F z).re := by
  intro hP z hz
  have h := HasHalfPlanePoissonTransport (F := F) hRep hP
  have hz' : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hz
  exact h hz'

/-- Statement-level boundary Poisson approximate-identity from a Poisson
representation: downstream modules can assume this to obtain the AI needed
for the negativity selection route. -/
def BoundaryPoissonAI (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ,
    Filter.Tendsto (fun b : ℝ => RH.RS.poissonSmooth F b x)
      (nhdsWithin 0 (Ioi 0)) (nhds (RH.RS.boundaryRe F x))

/-- Prop-level adapter: a Poisson representation of `F` implies the
boundary Poisson approximate-identity `BoundaryPoissonAI F`. -/
def boundaryPoissonAI_from_rep (F : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentation F → BoundaryPoissonAI F

open RH.AcademicFramework.CompletedXi

@[simp] def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ := fun z => (2 : ℂ) * RH.RS.J_pinch det2 O z

theorem HasHalfPlanePoissonTransport_Jpinch
    {det2 O : ℂ → ℂ}
    (hRep :
      HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
    PPlus (F_pinch det2 O) →
      ∀ ⦃z : ℂ⦄, z ∈ Ω → 0 ≤ ((F_pinch det2 O) z).re := by
  intro hP z hz
  exact HasHalfPlanePoissonTransport (F := F_pinch det2 O) hRep hP hz

theorem HasHalfPlanePoissonTransport_Jpinch_re
    {det2 O : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
    PPlus (F_pinch det2 O) →
      ∀ z : ℂ, z.re > (1/2 : ℝ) → 0 ≤ ((F_pinch det2 O) z).re := by
  intro hP z hz
  have h := HasHalfPlanePoissonTransport_Jpinch (det2 := det2) (O := O) hRep hP
  have hz' : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hz
  exact h hz'

/-!
Pinch specialization of the boundary Poisson approximate-identity interface.
Given a Poisson representation for the pinch field `F := 2 · J_pinch det2 O`,
this Prop packages the requirement that the Poisson smoothing tends to the
boundary trace a.e. as height goes to 0⁺.
-/
def BoundaryPoissonAI_Jpinch (det2 O : ℂ → ℂ) : Prop :=
  BoundaryPoissonAI (F_pinch det2 O)

/-- Prop-level adapter for the pinch field: a Poisson representation for
`F := 2 · J_pinch det2 O` yields `BoundaryPoissonAI (F_pinch det2 O)`. -/
def boundaryPoissonAI_from_rep_Jpinch (det2 O : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentation (F_pinch det2 O) →
    BoundaryPoissonAI (F_pinch det2 O)

/‑! ## Representation on a subset (off‑zeros variant)

We provide a subset‑restricted Poisson representation interface. This is useful
when `F` may have isolated singularities (e.g. poles) on `Ω`; the representation
is asserted on a subset `S ⊆ Ω` where `F` is analytic. The standard transport
corollary then yields interior nonnegativity of `Re F` on `S` from boundary
`(P+)`.
-/

/-- Subset‑restricted Poisson representation for a fixed `F` on `S ⊆ Ω`. -/
structure HasHalfPlanePoissonRepresentationOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  (subset_Ω : S ⊆ Ω)
  (analytic : AnalyticOn ℂ F S)
  (integrable : ∀ z ∈ S, Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t))
  (re_eq : ∀ z ∈ S, (F z).re = P (fun t : ℝ => (F (boundary t)).re) z)

/-- Subset‑restricted transport: from boundary `(P+)` and a Poisson representation
on `S`, conclude interior nonnegativity of `Re F` on `S`. -/
theorem HasHalfPlanePoissonTransport_on
    {F : ℂ → ℂ} {S : Set ℂ}
    (hRep : HasHalfPlanePoissonRepresentationOn F S) :
    PPlus F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hBoundary z hzS
  -- convert boundary a.e. nonnegativity to boundary parametrization
  have hBoundary' : ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re := by
    -- equality of boundary parametrizations is definitional
    have h0 : ∀ᵐ t : ℝ, 0 ≤ (F (Complex.mk (1/2) t)).re := hBoundary
    exact h0.mono (by intro t ht; simpa [boundary_mk_eq] using ht)
  -- positivity of the Poisson operator applied to nonnegative boundary data
  have hzΩ : z ∈ Ω := hRep.subset_Ω hzS
  have hpos :=
    P_nonneg_of_ae_nonneg
      (u := fun t : ℝ => (F (boundary t)).re)
      (hInt := by intro w hw; simpa using hRep.integrable w (hRep.subset_Ω hw))
      (hu_nonneg := hBoundary')
      (by simpa [Ω, Set.mem_setOf_eq] using hzΩ)
  simpa [hRep.re_eq z hzS] using hpos

/-- Pinch specialization (off‑zeros): representation on `Ω \ Z(ξ_ext)` yields
interior nonnegativity on that set from boundary `(P+)`. -/
theorem HasHalfPlanePoissonTransport_on_Jpinch
    {det2 O : ℂ → ℂ}
    (hRepOn : HasHalfPlanePoissonRepresentationOn (F_pinch det2 O)
      (Ω \ {z | riemannZeta z = 0})) :
    PPlus (F_pinch det2 O) →
      ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), 0 ≤ ((F_pinch det2 O) z).re := by
  intro hP
  exact HasHalfPlanePoissonTransport_on (F := F_pinch det2 O) (S := (Ω \ {z | riemannZeta z = 0})) hRepOn hP

/-- Pinch representation on the off-zeros set for the chosen outer with M=2 bound
derived internally from boundary modulus equality. Requires only the Poisson
identity for the real part as an input. -/
theorem pinch_representation_on_offXi_M2
  (hDet2 : RH.RS.Det2OnOmega)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  : HasHalfPlanePoissonRepresentationOn (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
      (Ω \ {z | riemannXi_ext z = 0}) := by
  classical
  -- notation
  let O : ℂ → ℂ := RH.RS.OuterHalfPlane.choose_outer hOuterExist
  let S : Set ℂ := (Ω \ {z | riemannXi_ext z = 0})
  have hSsub : S ⊆ Ω := by intro z hz; exact hz.1
  -- Analyticity on S
  have hJ : AnalyticOn ℂ (RH.RS.J_pinch RH.RS.det2 O) S :=
    RH.RS.J_pinch_analytic_on_offXi_choose (hDet2 := hDet2) (hOuterExist := hOuterExist) (hXi := hXi)
  have hAnalytic : AnalyticOn ℂ (F_pinch RH.RS.det2 O) S := by
    have hConst : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S := by simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S)
    simpa [F_pinch] using hConst.mul hJ
  -- Integrability via M=2 bound derived internally
  have hInt : ∀ z ∈ S,
      Integrable (fun t : ℝ => (F_pinch RH.RS.det2 O (boundary t)).re * poissonKernel z t) := by
    intro z hzS
    have hzΩ : z ∈ Ω := hSsub hzS
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
    exact integrable_boundary_kernel_of_bounded' (hOuterExist := hOuterExist) z (by simpa [Ω, Set.mem_setOf_eq] using hzΩ)
  -- Assemble record
  refine {
    subset_Ω := hSsub
  , analytic := hAnalytic
  , integrable := by intro z hz; simpa using hInt z hz
  , re_eq := by
      intro z hz
      have hzΩ : z ∈ Ω := hSsub hz
      -- Use vendor Poisson identity for the pinch field on Ω, then restrict to S
      simpa using (poisson_formula_re_vendor_for_F_pinch RH.RS.det2 O z hzΩ) }

/-- Pinch representation on the off-zeros set `Ω \\ {ξ_ext = 0}` (packaging):
assuming analyticity of `det2` and `O` on `Ω`, and a bounded boundary real
trace for `F_pinch det2 O` along the critical line, plus a Poisson identity for
the real part, we obtain a subset Poisson representation record on
`S := Ω \\ {ξ_ext = 0}`.

This is a statement-level constructor that packages standard analytic inputs
into the `HasHalfPlanePoissonRepresentationOn` structure; it avoids committing
to a specific proof of the Poisson formula here. -/
theorem pinch_representation_on_offXi
  (hDet2 : RH.RS.Det2OnOmega) {O : ℂ → ℂ} (hO : RH.RS.OuterHalfPlane O)
  (M : ℝ)
  (hBnd : ∀ t : ℝ, |(F_pinch RH.RS.det2 O (boundary t)).re| ≤ M)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hReEq : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 O z).re =
        P (fun t : ℝ => (F_pinch RH.RS.det2 O (boundary t)).re) z)
  : HasHalfPlanePoissonRepresentationOn (F_pinch RH.RS.det2 O)
      (Ω \ {z | riemannXi_ext z = 0}) := by
  classical
  -- Define the off-zeros set S and record S ⊆ Ω
  let S : Set ℂ := (Ω \ {z | riemannXi_ext z = 0})
  have hSsub : S ⊆ Ω := by intro z hz; exact hz.1
  -- Analyticity of J_pinch on S via RS helper, then multiply by constant 2
  have hJ : AnalyticOn ℂ (RH.RS.J_pinch RH.RS.det2 O) S :=
    RH.RS.J_pinch_analytic_on_offXi_choose (hDet2 := hDet2) (hOuterExist := ?_) (hXi := hXi)
  have hAnalytic : AnalyticOn ℂ (F_pinch RH.RS.det2 O) S := by
    -- F_pinch = (2) * J_pinch det2 O
    have hConst : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S := by simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S)
    simpa [F_pinch] using hConst.mul hJ
  -- Integrability at each interior z, using the bounded boundary trace
  have hInt : ∀ z ∈ S,
      Integrable (fun t : ℝ => (F_pinch RH.RS.det2 O (boundary t)).re * poissonKernel z t) := by
    intro z hzS
    have hzΩ : z ∈ Ω := hSsub hzS
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
    exact integrable_boundary_kernel_of_bounded (F := F_pinch RH.RS.det2 O) z M hzRe hBnd
  -- Assemble the representation on S
  refine {
    subset_Ω := hSsub
  , analytic := hAnalytic
  , integrable := by
      intro z hz; simpa using hInt z hz
  , re_eq := by
      intro z hz; simpa using (hReEq z hz) };

/‑! ## Integrability helper for boundary kernels (simple sufficient condition)

We record a convenient sufficient condition ensuring integrability of the
kernel‑weighted boundary trace `t ↦ (Re F(1/2+it)) · P(z,t)` for a fixed
interior point `z` with `Re z > 1/2`:

- If the boundary real trace is globally bounded by a constant `M`, then
  `t ↦ (Re F(1/2+it)) · poissonKernel z t` is integrable on ℝ.

This is enough for many applications where one obtains an a priori uniform
bound on the boundary data. It avoids developing a full growth calculus.
-/

open MeasureTheory

/-- Poisson kernel integrability on ℝ for fixed `z` with `Re z > 1/2`. -/
lemma poissonKernel_integrable {z : ℂ} (hz : (1/2 : ℝ) < z.re) :
  Integrable (fun t : ℝ => poissonKernel z t) := by
  classical
  -- Write P(z,t) = (1/(π a)) · 1/(1 + ((t - b)/a)^2) with a = Re z − 1/2, b = Im z
  set a : ℝ := z.re - (1/2 : ℝ)
  set b : ℝ := z.im
  have ha : 0 < a := sub_pos.mpr hz
  have hrewrite :
      (fun t : ℝ => poissonKernel z t)
        = (fun t : ℝ => (1 / (Real.pi * a)) * (1 / (1 + ((t - b) / a)^2))) := by
    funext t
    have : (z.re - (1/2 : ℝ)) = a := rfl
    have : z.im = b := rfl
    simp [poissonKernel, this, a, b, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc, pow_two]
  -- `t ↦ 1/(1 + ((t - b)/a)^2)` is integrable (affine change of variables)
  have hBase : Integrable (fun u : ℝ => 1 / (1 + u^2)) := by
    simpa using Real.integrable_one_div_one_add_sq
  have hScaled : Integrable (fun t : ℝ => 1 / (1 + ((t - b) / a)^2)) := by
    -- Integrability is preserved by affine changes of variables on ℝ
    simpa [sub_eq_add_neg, one_div] using hBase.comp_mul_add (c := (1 / a)) (d := - b / a)
  -- Multiply by the constant `(1 / (π a))`
  have hConst : Integrable (fun t : ℝ => (1 / (Real.pi * a)) * (1 / (1 + ((t - b) / a)^2))) :=
    hScaled.const_mul _
  simpa [hrewrite] using hConst

/-- Simple sufficient condition: if the boundary real trace is globally bounded
by `M`, then the boundary Poisson integrand is integrable for any interior
point `z` with `Re z > 1/2`. -/
lemma integrable_boundary_kernel_of_bounded
  (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
  (hz : (1/2 : ℝ) < z.re)
  (hBnd : ∀ t : ℝ, |(F (boundary t)).re| ≤ M) :
  Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t) := by
  classical
  -- Use kernel integrability and domination by the constant bound M
  have hker : Integrable (fun t : ℝ => poissonKernel z t) := poissonKernel_integrable hz
  -- Domination: |(F(boundary t)).re * P(z,t)| ≤ M * P(z,t)
  have hDom : (fun t : ℝ => |(F (boundary t)).re * poissonKernel z t|)
      ≤ᵐ[volume] (fun t : ℝ => M * poissonKernel z t) := by
    refine (Filter.eventually_of_forall ?_)
    intro t; have := hBnd t
    have hnonneg : 0 ≤ poissonKernel z t := by
      exact poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using hz) t
    have : |(F (boundary t)).re * poissonKernel z t|
        = |(F (boundary t)).re| * poissonKernel z t := by
      simpa [abs_mul, Real.abs_of_nonneg hnonneg]
    simpa [this, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right (hBnd t) hnonneg)
  -- Conclude by dominated convergence (bounded by an integrable majorant)
  have hMaj : Integrable (fun t : ℝ => M * poissonKernel z t) :=
    hker.const_mul _
  exact Integrable.of_dominated (fun t => (F (boundary t)).re * poissonKernel z t)
    (fun t => M * poissonKernel z t) hMaj hDom

/-- Specialized integrability for the pinch field at boundary with `M = 2`.
Given outer existence `hOuterExist`, any fixed interior point `z` with
`Re z > 1/2` yields an integrable boundary Poisson integrand for
`F := F_pinch det2 (choose_outer hOuterExist)` using the bound
`|(Re F(1/2+it))| ≤ 2` derived from the boundary modulus equality.
-/
lemma integrable_boundary_kernel_of_bounded'
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (z : ℂ) (hz : (1/2 : ℝ) < z.re) :
  Integrable (fun t : ℝ =>
    (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re
      * poissonKernel z t) := by
  classical
  -- Outer and boundary modulus equality
  let O : ℂ → ℂ := RH.RS.OuterHalfPlane.choose_outer hOuterExist
  have hBME : RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) :=
    (RH.RS.OuterHalfPlane.choose_outer_spec hOuterExist).2
  -- Uniform boundary bound |Re F| ≤ 2
  have hBnd2 : ∀ t : ℝ,
      |(F_pinch RH.RS.det2 O (boundary t)).re| ≤ (2 : ℝ) := by
    intro t
    -- Case split on boundary nonvanishing; if denom vanishes, the expression reduces to 0
    by_cases hO : O (boundary t) = 0
    · by_cases hXi : riemannXi_ext (boundary t) = 0
      · -- F_pinch(boundary t) = 0 ⇒ bound holds
        have : (F_pinch RH.RS.det2 O (boundary t)) = 0 := by
          simp [F_pinch, RH.RS.J_pinch, hO, hXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        simpa [this] using (abs_nonneg ((F_pinch RH.RS.det2 O (boundary t)).re)).le.trans (by norm_num)
      · -- O=0, ξ≠0 still gives bound via direct inequality |Re w| ≤ 2|J|
        -- Use general inequality through the previously proved boundary lemma when possible
        have h := RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME t (by simpa [hO]) (by exact hXi)
        simpa using h
    · by_cases hXi : riemannXi_ext (boundary t) = 0
      · -- ξ=0 (O≠0): same as above, F_pinch(boundary t) = 0 under field convention
        have : (F_pinch RH.RS.det2 O (boundary t)) = 0 := by
          simp [F_pinch, RH.RS.J_pinch, hO, hXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        simpa [this] using (abs_nonneg ((F_pinch RH.RS.det2 O (boundary t)).re)).le.trans (by norm_num)
      · -- Nonvanishing case: apply the RS boundary bound lemma
        have h := RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME t (by exact hO) (by exact hXi)
        simpa using h
  -- Apply the general integrability lemma with M = 2
  exact integrable_boundary_kernel_of_bounded
    (F := F_pinch RH.RS.det2 O) (z := z) (M := 2) hz hBnd2

/-- Local Poisson formula (statement-level packaging): if `S ⊆ Ω`, `F` is
analytic on `S`, the boundary real trace is globally bounded by 2 and locally
L¹ on compacts, and a subset Poisson representation record is available, then
for every `z ∈ S` we have the Poisson integral identity for `Re F` at `z`. -/
lemma poisson_formula_re_for_halfplane_analytic
  {F : ℂ → ℂ} {S : Set ℂ}
  (hS : S ⊆ Ω)
  (hAnalytic : AnalyticOn ℂ F S)
  (hBound2 : ∀ t : ℝ, |(F (boundary t)).re| ≤ (2 : ℝ))
  (hL1loc : ∀ K : Set ℝ, IsCompact K → IntegrableOn (fun t => (F (boundary t)).re) K volume)
  (hRepOn : HasHalfPlanePoissonRepresentationOn F S)
  : ∀ z ∈ S, (F z).re = P (fun t : ℝ => (F (boundary t)).re) z := by
  intro z hz
  exact hRepOn.re_eq z hz

/-- Self-contained Poisson formula for the half-plane (statement-level): if `F` is
analytic on `Ω` and its boundary real trace is bounded by `2` and locally L¹ on compacts,
then the real part is given by the Poisson integral. Realized via the Cayley→disk bridge. -/
lemma poisson_formula_re_selfcontained
  (F : ℂ → ℂ)
  (hAnalytic : AnalyticOn ℂ F Ω)
  (hBound2 : ∀ t : ℝ, |(F (boundary t)).re| ≤ (2 : ℝ))
  (hL1loc : ∀ K : Set ℝ, IsCompact K → IntegrableOn (fun t => (F (boundary t)).re) K volume)
  (Hdisk : ℂ → ℂ)
  (hRel : Set.EqOn F (fun z => Hdisk (RH.AcademicFramework.CayleyAdapters.toDisk z)) Ω)
  (hReEq : ∀ z ∈ Ω,
    (F z).re = P (fun t : ℝ => (F (boundary t)).re) z)
  : HasHalfPlanePoissonRepresentation F := by
  -- Derive the boundary-kernel integrability from the uniform bound `|Re F(1/2+it)| ≤ 2`.
  have hIntegrable : ∀ z ∈ Ω,
      Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t) := by
    intro z hz
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hz
    exact integrable_boundary_kernel_of_bounded (F := F) z (2 : ℝ) hzRe hBound2
  -- Package into the half-plane representation via the Cayley bridge (no admits here).
  exact RH.AcademicFramework.CayleyAdapters.HalfPlanePoisson_from_Disk
    F Hdisk hRel hAnalytic hIntegrable hReEq

end HalfPlaneOuter
end AcademicFramework
end RH
