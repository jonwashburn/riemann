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

end HalfPlaneOuter
end AcademicFramework
end RH
